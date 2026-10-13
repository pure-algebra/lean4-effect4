import Tools.View.Tube.Score
import Tools.View.Tube.Queue
import Tools.View.Tube.Measure

open Tools.View Tools.View.Tube

#guard (Score.record Score.twoChildren).all fun r =>
  (Score.film "board-score" r).toOption.any (fun svg => (SvgOut.fileText svg).isOk) &&
    (SvgOut.fileText (Score.endStill r)).isOk
#guard (Queue.record CellSheet.scene).toOption.all fun (l, fs) =>
  (Queue.film "board-queue" l (fs.map (·.2))).toOption.any
    (fun svg => (SvgOut.fileText svg).isOk) &&
    (SvgOut.fileText (Queue.endStill l (fs.map (·.2)))).isOk
#guard (Queue.record CellSheet.large).toOption.all fun (l, fs) =>
  (Queue.film "board-large" l (fs.map (·.2))).isOk

-- The tree's own measurement counts animations and all written path bytes.
#eval (Score.record Score.twoChildren).bind fun r =>
  (Score.film "board-score" r).toOption.map fun film =>
    (film.render.utf8ByteSize, Measure.costOf film.toRaw)
#eval (Queue.record CellSheet.scene).toOption.bind
  fun (entry : Queue.Layout × List (String × Marking)) =>
    let (l, fs) := entry
    (Queue.film "board-queue" l (fs.map (fun (pair : String × Marking) => pair.2))).toOption.map
      fun film => (film.render.utf8ByteSize, Measure.costOf film.toRaw)
#eval (Queue.record CellSheet.large).toOption.bind
  fun (entry : Queue.Layout × List (String × Marking)) =>
    let (l, fs) := entry
    (Queue.film "board-large" l (fs.map (fun (pair : String × Marking) => pair.2))).toOption.map
      fun film => (film.render.utf8ByteSize, Measure.costOf film.toRaw)
