// Retargeted from foldlab experiments/parser-census/src/census-contract.ts at 4005d34f.
// Declaration metadata is distinct from the ingestion units that define the score.
import { Schema } from "effect"
export const DeclKind = Schema.Literals(["variable", "function", "class", "interface", "typeAlias", "enum", "module"])
export const Decl = Schema.Struct({ kind: DeclKind, name: Schema.String, exported: Schema.Boolean, ambient: Schema.Boolean, variance: Schema.Boolean })
export type Decl = typeof Decl.Type
export const decodeDecls = Schema.decodeUnknownSync(Schema.Array(Decl))
export const ANONYMOUS_DEFAULT = "default"
export const DESTRUCTURED = "«destructured»"
export const Generation = Schema.Literals(["v4", "v3", "pre-v3"])
export type Generation = typeof Generation.Type
export const Metrics = Schema.Struct({ files: Schema.Number, bytes: Schema.Number, reads: Schema.Number, parseUs: Schema.Number, totalUs: Schema.Number })
export type Metrics = typeof Metrics.Type
export const Project = Schema.Struct({ id: Schema.String, pin: Schema.String, labels: Schema.Array(Schema.String), localPath: Schema.String })
export type Project = typeof Project.Type
export const Manifest = Schema.Struct({ projects: Schema.Array(Project) })
export const Labels = Schema.Struct({ labelVocabulary: Schema.Record(Schema.String, Schema.String) })
export interface Bucket { candidates: number; lifted: number; refused: number; disagree: number; codes: Record<string, number>; heads: Record<string, number> }
