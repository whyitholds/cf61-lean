import AutoCert11
import AutoCert16
import AutoCert19
import AutoCert26
import ClosedForm

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem closedR1Cert (k l t : Nat) : autoDen closedR1F k l t :=
  autoUnNarrow closedR1F k l t (autoFinish autoOk147 k l t)

theorem closedR2Cert (k l t : Nat) : autoDen closedR2F k l t :=
  autoUnNarrow closedR2F k l t (autoFinish autoOk236 k l t)

theorem closedR3Cert (k l t : Nat) : autoDen closedR3F k l t :=
  autoUnNarrow closedR3F k l t (autoFinish autoOk276 k l t)

theorem closedR4Cert (k l t : Nat) : autoDen closedR4F k l t :=
  autoUnNarrow closedR4F k l t (autoFinish autoOk365 k l t)
