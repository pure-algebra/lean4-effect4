import Tools.Session
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Program.Definitions
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Program.Folds.TyCache
import Effect4.Laws.Program.Typing.Call
import Effect4.Laws.Api.Live
import Effect4.Laws.Api.HostSession
import Effect4.Laws.Run
import Effect4.Laws.Run.Journal
import Effect4.Laws.Run.Tape
import Effect4.Laws.Run.Tree
import Effect4.Laws.Machine.Approximation
import ProofGraph.Plan

/-!
# Probe Status: the measured standing of every existing node of the proof DAG

Each name below is an existing declaration that the scout's DAG uses. `#plan_status` reads its
standing from its proof: proved, modulo the planned goals it rests on, or a goal. The counts of
lemmas and definitions are relative to this file's root and are not read.
-/

-- Slice A and B: the edit route
#plan_status Effect4.Program.Sketch.check_fill_focusAt Effect4.Program.Sketch.check_omit_focusAt
  Effect4.Program.Sketch.fillAt_of_replaceAt Effect4.Program.Node.replaceAt_eff
  Effect4.Program.SourceSession.feed_coherent Effect4.Program.SourceSession.feed_keeps
  Effect4.Program.SourceSession.view_type Effect4.Program.SourceSession.reached_view
  Effect4.Program.SourceSession.focusAt_typed Effect4.Program.Sketch.sourceCheck_toOption
  Effect4.Program.Sketch.sourceRefusals_head Tools.Query.fillPremises_sound
  Effect4.Program.admitProgram_eq_ok Effect4.Program.Sketch.decode_exact
  Effect4.Program.SourceSession.feed_undo

-- Slice C: the verdict cache
#plan_status Effect4.Program.Checker.check_rebase Effect4.Program.tableAt_rebase
  Effect4.Program.check_ext Effect4.Program.check_restrict Effect4.Program.SigApp.withHoles_extends
  Effect4.Program.SigExtends.withDefs Effect4.Program.SigExtends.withParams
  Effect4.Program.TyCache.check_agreement

-- Slice D: the fill set
#plan_status Effect4.Program.Sketch.table_fill Effect4.Program.Sketch.check_fill_kept
  Effect4.Program.Sketch.fillAt_some Effect4.Program.Sketch.focusAt_at
  Effect4.Program.Table.typedAt_table Effect4.Program.Table.typedAt_table_of_focusAt
  Effect4.Program.tableAt_path Effect4.Program.Table.under_append Effect4.Program.Path.prefix_cases
  Effect4.Program.Node.at_replaceAt_disjoint Effect4.Program.Node.replaceAt_cons_isBlock
  Effect4.Program.Node.replaceAt_defs_main Effect4.Program.Node.replaceAt_defs_body
  Effect4.Program.Node.replaceAt_effs_head Effect4.Program.Node.replaceAt_effs_tail
  Effect4.Program.Node.replaceAt_layers_cons Effect4.Program.defs_replaceAt_layers
  Effect4.Program.Eff.partAt_plain Effect4.Program.Eff.eq_defs_of_isBlock

-- Slice E: the live session and the preview
#plan_status Effect4.Live.journal_replays Effect4.Live.feedAll_wire Effect4.Live.replay_recorded
  Effect4.Live.start_ok Effect4.Live.start_error Effect4.Live.reached Effect4.Run.journal_replays
  Effect4.Run.admitted_unique Effect4.Api.HostSession.readReply_store_other
  Effect4.Api.HostSession.submit_key_independence Effect4.Api.HostSession.reply_commute
  Effect4.Run.session_keys_once Effect4.Run.Tree.settle_sound Effect4.Run.Tree.probe_stable
  Effect4.Live.view_awaits Effect4.Live.view_checked

-- Slices F to H: what they would build on
#plan_status Effect4.Program.check_weaken Effect4.Program.effTy_weaken
  Effect4.Program.references_move Effect4.Program.callAt_rowTy Effect4.Program.hom_eq_cata_eff
  Effect4.Run.tape_replays Effect4.Run.funded_replays Effect4.Machine.replayEval_append
  Effect4.Run.tapeFrom_position_replays
