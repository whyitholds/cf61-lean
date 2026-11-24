import ClosedIndSlim
import ClosedLink
import AutoClosed

theorem cfCheckedClosed : CF61_Closed := by
  apply cfClosedFromLocal
  intro m _
  apply clGoalsLocal _ m
  intro r k L t hr hu
  interval_cases r
  · exact closedR1Cert k L t
  · exact closedR2Cert k L t
  · exact closedR3Cert k L t
  · exact closedR4Cert k L t
