import PartII
import NumBits
import CoordsBase

theorem cfPartIIFromClosed (hc : CF61_Closed) : CF61_PartII :=
  cfPartIIWithBits cfZBit cfCoords hc
