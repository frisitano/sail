enum StopReason = { Stop }

type PackedInt = {'n, true. atom('n)}

val stop : forall ('a : Type). StopReason -> 'a
function stop(_reason) = exit(())

function choose(flag : bool) -> PackedInt =
  if flag then 0 else stop(Stop)
