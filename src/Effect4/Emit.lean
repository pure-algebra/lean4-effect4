import Effect4.Codegen.Print
import Effect4.Codegen.PrintTyped
import Effect4.Codegen.Checked
import Effect4.Codegen.Schema
import Effect4.Codegen.Target
import Effect4.Schema.Document
import Effect4.Schema.Codec
import Effect4.Api.RunnerBytes

/-!
# Effect4.Emit — the entry module for what leaves the tree (decisions row 332)

A TypeScript client or a code generator imports this module. It re-exports:

- printing a program to TypeScript, with a call's type arguments at a join, and checked
  module production (`Codegen.Print`, `Codegen.PrintTyped`, `Codegen.Checked`, `Codegen.Target`);
- Schema documents and their TypeScript (`Schema.Document`, `Codegen.Schema`);
- the type-directed JSON codec (`Schema.Codec`);
- the runner's byte boundary, with each answer's canonical schema (`Api.RunnerBytes`).

It declares nothing.
-/
