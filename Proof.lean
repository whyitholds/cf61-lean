import Statement
import CoordsBase
import ClosedResult
import PartIIResult
import SharpBase
import PartIFull
import UlamExist
import MainReduction

open OneAdd CF61

theorem proof_coords : CF61_Coords := cfCoords

theorem proof_closed : CF61_Closed := cfCheckedClosed

theorem proof_sharp : CF61_Sharp := cfSharpOfClosed proof_closed

theorem proof_partII : CF61_PartII := cfPartIIFromClosed proof_closed

theorem proof_partI : CF61_PartI := cfPartIFromClosed proof_closed

theorem proof_main : CF61_Main := cfMainOfParts cfUlamExists proof_partI proof_partII
