/* e4val.h -- the Val wire frames in C: the value tree, its reader and its writer.

   What it is: a C reading of `Store.Val` (src/Effect4/Store/Carrier/Val.lean). Every frame is
   `tag :: be64 length ++ payload`; the tag bytes are `Store.Tag`'s. The reader transcribes
   `Val.decode` (readFrame, decodeSeq, decodeBody, decodeOne) and refuses what it refuses, with a
   located refusal: the byte offset, the path of child positions, and a reason. The writer
   transcribes `Val.encode`. The C tree is wider than Lean's `Val` (a C caller can build a natural
   with a leading zero byte, a string that is not UTF-8, an integral double in the binary64 frame),
   so the writer checks a tree first, as `Val.encode?` does, and refuses one outside the image.

   Properties:
   V1  e4_decode accepts exactly the bytes Lean's `Val.decode` accepts, inside the nesting limit
       E4_MAX_DEPTH.                                    tested on the committed fixtures and on
                                                        the refusals that Val.lean's guards pin
   V2  Exactness: for accepted bytes b, e4_encode(e4_decode(b)) = b.       tested
   V3  Retraction: for a tree that e4_check admits, e4_decode(e4_encode(v)) equals v.  tested
   V4  A natural, a string, bytes, a digest and a handle's index are borrowed slices of the input:
       the reader copies no payload.                    by construction
   V5  Nesting deeper than E4_MAX_DEPTH is refused with its own reason. Lean's decoder has no such
       limit, so V1 holds only inside it.               by construction

   What it does not establish: any property of a value's meaning (membership in a `Ty`); that is
   the codec of the type (see e4host.h). */

#ifndef E4VAL_H
#define E4VAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* The tag alphabet, `Store.Tag` in Val.lean. Appended, never renumbered. */
enum {
  E4_BOOL = 1, E4_NAT = 2, E4_STRING = 3, E4_LIST = 4, E4_PAIR = 5, E4_NONE = 6, E4_SOME = 7,
  E4_BYTES = 8, E4_UNIT = 9, E4_CTOR = 10, E4_REF = 11, E4_HANDLE = 12, E4_INT = 13,
  E4_FLOAT = 14
};

/* A borrowed byte slice. A string is strict UTF-8 and is not NUL-terminated: U+0000 is a member
   of a Lean `String`. */
typedef struct {
  const uint8_t *ptr;
  size_t len;
} e4_slice;

typedef struct e4_val e4_val;

struct e4_val {
  uint8_t tag;
  union {
    bool b;                                /* E4_BOOL */
    e4_slice digits;                       /* E4_NAT, E4_INT: big-endian, no leading zero;
                                              E4_INT holds n for the integer -(n+1) */
    e4_slice str;                          /* E4_STRING */
    e4_slice bytes;                        /* E4_BYTES */
    struct { e4_val *items; size_t count; } list;        /* E4_LIST */
    struct { e4_val *fst; e4_val *snd; } pair;           /* E4_PAIR */
    e4_val *some;                                        /* E4_SOME */
    struct { e4_slice index; e4_val *args; size_t count; } ctor;  /* E4_CTOR: index digits */
    struct { uint8_t kind; e4_slice digest; } ref;       /* E4_REF */
    struct { uint8_t kind; e4_slice index; } handle;     /* E4_HANDLE: index digits */
    uint64_t bits;                                       /* E4_FLOAT: binary64 bit pattern */
  } as;
};

/* An arena: every node the reader builds, and every node a host builds, lives in one. */
typedef struct e4_arena_block e4_arena_block;
typedef struct {
  e4_arena_block *head;
} e4_arena;

void e4_arena_init(e4_arena *a);
void e4_arena_free(e4_arena *a);
void *e4_arena_alloc(e4_arena *a, size_t size);

/* A located refusal: where in the input, at which child position, and why. */
#define E4_PATH_MAX 32
typedef struct {
  size_t offset;               /* the byte offset of the frame or byte refused */
  size_t depth;                /* the number of child positions on the path */
  size_t path[E4_PATH_MAX];    /* the child positions from the root, the first E4_PATH_MAX */
  const char *reason;
} e4_refusal;

#define E4_MAX_DEPTH 4096

/* The exact reader: the whole input is one frame and nothing else. Returns the value, or NULL with
   the refusal filled in. */
e4_val *e4_decode(e4_arena *a, const uint8_t *in, size_t len, e4_refusal *why);

/* A growable output buffer. */
typedef struct {
  uint8_t *ptr;
  size_t len;
  size_t cap;
} e4_buf;

void e4_buf_free(e4_buf *b);
void e4_buf_append(e4_buf *b, const void *p, size_t n);

/* The checker of a C-built tree: NULL when the tree is in the image of `Val.encode` on well-formed
   values, or the reason it is not. `path` receives the child positions of the refused node. */
const char *e4_check(const e4_val *v, e4_refusal *why);

/* The checked writer: appends the frames of v to out, after e4_check. Returns false with the
   refusal when the check refuses; out is unchanged then. */
bool e4_encode(const e4_val *v, e4_buf *out, e4_refusal *why);

/* Structural equality of two trees, by their fields. */
bool e4_equal(const e4_val *x, const e4_val *y);

/* The value as the Lean syntax that builds it, as `Val.render` writes it. */
void e4_render(const e4_val *v, e4_buf *out);

/* Constructors for a host. Slices are borrowed, not copied: they must outlive the value. */
e4_val *e4_mk_unit(e4_arena *a);
e4_val *e4_mk_bool(e4_arena *a, bool b);
e4_val *e4_mk_nat_u64(e4_arena *a, uint64_t n);
e4_val *e4_mk_str(e4_arena *a, const uint8_t *ptr, size_t len);
e4_val *e4_mk_none(e4_arena *a);
e4_val *e4_mk_some(e4_arena *a, e4_val *inner);
e4_val *e4_mk_pair(e4_arena *a, e4_val *fst, e4_val *snd);
e4_val *e4_mk_list(e4_arena *a, size_t count);   /* items to be filled by the caller */
e4_val *e4_mk_ctor_u64(e4_arena *a, uint64_t index, size_t count);

/* A natural's digits as a uint64_t: false when it has more than eight digits. This map from the
   natural numbers into uint64_t is a refusal outside [0, 2^64). */
bool e4_nat_u64(e4_slice digits, uint64_t *out);

/* The binary64 frame's domain, `Val.floatFrame`: the doubles not stored as an integer image. */
bool e4_float_frame(uint64_t bits);

/* Strict UTF-8 as `utf8Chars` reads it (src/Effect4/Store/Carrier/Utf8.lean): shortest forms,
   no surrogates, at most U+10FFFF. Returns the offset of the first refused byte, or len. */
size_t e4_utf8_prefix(const uint8_t *p, size_t len);

/* Lowercase hexadecimal, both ways. e4_unhex returns false on an odd length or a non-hex digit. */
bool e4_unhex(const char *hex, size_t hexlen, e4_buf *out);
void e4_hex(const uint8_t *p, size_t len, e4_buf *out);

#endif
