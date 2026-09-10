"""Selected source descriptions and the frozen OCaml engine's actual declarations.

The producer reads both inputs. It never supplies a missing target constructor or
execution permission. Unsupported payload changes and ambiguous declarations refuse.
"""
from dataclasses import dataclass
import re

@dataclass(frozen=True)
class Declaration:
    head: str
    body: str

def declarations(source):
    # OCaml comments can nest; blank them without changing declaration line starts.
    chars = list(source)
    depth = 0
    i = 0
    while i < len(chars):
        if source.startswith('(*', i):
            depth += 1
            chars[i:i+2] = [' ', ' ']
            i += 2
        elif depth and source.startswith('*)', i):
            depth -= 1
            chars[i:i+2] = [' ', ' ']
            i += 2
        else:
            if depth and chars[i] != '\n': chars[i] = ' '
            i += 1
    if depth: raise ValueError('unterminated engine comment')
    source = ''.join(chars)
    matches = list(re.finditer(r'(?m)^(?:type|and)\s+([^=\n]+?)\s*=', source))
    result = {}
    for i, match in enumerate(matches):
        name = match[1].strip().split()[-1]
        end = matches[i+1].start() if i+1 < len(matches) else len(source)
        body = source[match.end():end]
        cut = re.search(r'(?m)^(?:let|module|end)\b', body)
        if cut: body = body[:cut.start()]
        if name in result: raise ValueError('ambiguous engine declaration: ' + name)
        result[name] = Declaration(match[1].strip(), body.strip())
    return result

def split_top(text, separator='*'):
    depth = 0
    start = 0
    out = []
    for i, char in enumerate(text):
        if char == '(': depth += 1
        elif char == ')': depth -= 1
        elif char == separator and depth == 0:
            out.append(text[start:i].strip()); start = i+1
        if depth < 0: raise ValueError('unbalanced type parentheses')
    if depth: raise ValueError('unbalanced type parentheses')
    return out + [text[start:].strip()]

def type_shape(text):
    text = ' '.join(text.split())
    parts = split_top(text)
    if len(parts) > 1: return ('prod', tuple(type_shape(p) for p in parts))
    if text.startswith('(') and text.endswith(')'):
        return type_shape(text[1:-1])
    for suffix in [' option', ' list']:
        if text.endswith(suffix): return (suffix.strip(), type_shape(text[:-len(suffix)]))
    if text == "'op": return ('parameter', 'op')
    if text.startswith("'op "): return ('applied', text[4:])
    if re.fullmatch(r'[a-z][a-z0-9_]*', text): return ('name', text)
    raise ValueError('unsupported engine type: ' + text)

def snake(name):
    return re.sub(r'(?<!^)(?=[A-Z])', '_', name).lower()

def expected_shape(shape, families, parameters=()):
    kind = shape['kind']
    scalar = {'nat':'int','bool':'bool','string':'string','unit':'unit'}
    if kind in scalar: return ('name', scalar[kind])
    if kind in {'list','option'}: return (kind, expected_shape(shape['inner'], families, parameters))
    if kind == 'prod':
        return ('prod', (expected_shape(shape['left'], families, parameters), expected_shape(shape['right'], families, parameters)))
    if kind == 'canonicalRow': return ('list', expected_shape(shape['inner'], families, parameters))
    if kind == 'nominal':
        if shape['name'] in parameters and not shape['parameters']:
            if list(parameters) != ['Effect4.Program.NativeOp']:
                raise ValueError('unsupported engine parameter carrier')
            return ('parameter', 'op')
        target = families.get(shape['name'])
        if target is None: raise ValueError('unselected source nominal: ' + shape['name'])
        if shape['parameters']:
            if len(shape['parameters']) != 1 or shape['parameters'][0].get('name') != 'Effect4.Program.NativeOp':
                raise ValueError('unsupported engine parameter projection: ' + shape['name'])
            return ('applied', target['label'])
        return ('name', target['label'])
    raise ValueError('unsupported source shape: ' + kind)

def engine_constructors(body):
    arms = [arm.strip() for arm in body.split('|') if arm.strip()]
    result = []
    for arm in arms:
        match = re.fullmatch(r'([A-Z][A-Za-z0-9_]*)(?:\s+of\s+(.+))?', arm, re.S)
        if not match: raise ValueError('unsupported engine constructor: ' + arm)
        fields = [] if match[2] is None else split_top(match[2])
        result.append((match[1].split('_',1)[-1], [type_shape(field) for field in fields]))
    return result

def selected_view(descriptor, engine):
    if descriptor.get('format') != 'effect4-program-structure-v1' or descriptor.get('phase') != 'ground-source-declaration':
        raise ValueError('unsupported structural description format/phase')
    source = [f for block in descriptor['blocks'] for f in block]
    families = {f['name']:f for f in source}
    if len(families) != len(source) or len({f['label'] for f in source}) != len(source):
        raise ValueError('duplicate selected source family')
    actual = declarations(engine)
    common = []
    boundaries = []
    for family in source:
        name = family['label']; path = family['name']
        declaration = actual.get(name)
        if declaration is None:
            boundaries.append({'family':path,'reason':'absent-frozen-engine-family'}); continue
        constructors = family['constructors']
        if [c['ordinal'] for c in constructors] != list(range(len(constructors))):
            raise ValueError(path + ': invalid source ordinals')
        if family['structure']:
            if len(constructors) != 1: raise ValueError(path + ': structure arity')
            fields = constructors[0]['fields']
            body = declaration.body
            if body.startswith('{') and body.endswith('}'):
                target_fields = []
                for field in body[1:-1].split(';'):
                    if not field.strip(): continue
                    key, sep, value = field.partition(':')
                    if not sep: raise ValueError(path + ': malformed engine field')
                    target_fields.append((key.strip(), type_shape(value)))
                expected = [(snake(f['name']), expected_shape(f['shape'], families, family['parameters'])) for f in fields]
                # Record-only append shortages remain unavailable to this frozen engine;
                # a changed/reordered existing field must stop the producer.
                if len(target_fields) > len(expected) or target_fields != expected[:len(target_fields)]:
                    raise ValueError(path + ': engine structure field order/payload differs')
                if target_fields != expected:
                    boundaries.append({'family':path,'reason':'source-structure-append-unavailable-in-frozen-engine',
                                       'engine':len(target_fields),'source':len(expected)})
            elif len(fields) == 1 and fields[0]['name'] == 'value' and type_shape(body) == expected_shape(fields[0]['shape'], families, family['parameters']):
                pass  # Explicit single-field wrapper erasure at the engine projection.
            else: raise ValueError(path + ': unsupported engine structure projection')
            common.append((family, declaration, [])); continue
        target = engine_constructors(declaration.body)
        if len(target) > len(constructors): raise ValueError(path + ': engine has an unknown constructor')
        for i, (ctor_name, fields) in enumerate(target):
            src = constructors[i]
            expected = [expected_shape(f['shape'], families, family['parameters']) for f in src['fields']]
            if ctor_name != src['name'].rsplit('.',1)[-1] or fields != expected:
                raise ValueError(f'{path}.constructor[{i}]: engine ordinal/payload differs')
        if len(target) != len(constructors):
            boundaries.append({'family':path,'reason':'source-append-unavailable-in-frozen-engine',
                               'engine':len(target),'source':len(constructors)})
        common.append((family, declaration, [name for name,_ in target]))
    if not common: raise ValueError('empty engine intersection')
    return common, boundaries
