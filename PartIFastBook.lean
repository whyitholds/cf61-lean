import PartIFastCore
import PartIFastData
set_option maxRecDepth 100000
set_option maxHeartbeats 0


def pfPass (i : Nat) : Bool :=
  let v := pfRows[i]!
  let e := pfEdges[i]!
  pfGood v && ((decide (e[0]! < 683) && pfTr0 false v pfRows[e[0]!]!) && ((decide (e[1]! < 683) && pfTr1 false v pfRows[e[1]!]!) && ((decide (e[2]! < 683) && pfTr2 false v pfRows[e[2]!]!) && ((decide (e[3]! < 683) && pfTr3 false v pfRows[e[3]!]!) && true))))
