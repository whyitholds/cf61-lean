import PartIMathematical
import PartIFastFinal

theorem cfPartIFromClosed (closed : CF61_Closed) : CF61_PartI :=
  piPartIByGraph closed piFastFirst piFastAll
