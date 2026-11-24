import PartIFastT0
import PartIFastT1
import PartIFastT2
import PartIFastT3
import PartIFastT4
import PartIFastT5
import PartIFastT6
import PartIFastT7
import PartIFastT8
import PartIFastT9
import PartIFastT10
import PartIFastT11
import PartIFastT12
import PartIFastT13
import PartIFastT14
import PartIFastT15
import PartIFastT16
import PartIFastT17
import PartIFastT18
import PartIFastT19
import PartIFastT20
import PartIFastT21

theorem pfTAll : pfTRange 0 683 :=
  (pfTJoin 0 352 331 (pfTJoin 0 160 192 (pfTJoin 0 64 96 (pfTJoin 0 32 32 pfTGroup0 pfTGroup1) (pfTJoin 64 32 64 pfTGroup2 (pfTJoin 96 32 32 pfTGroup3 pfTGroup4))) (pfTJoin 160 96 96 (pfTJoin 160 32 64 pfTGroup5 (pfTJoin 192 32 32 pfTGroup6 pfTGroup7)) (pfTJoin 256 32 64 pfTGroup8 (pfTJoin 288 32 32 pfTGroup9 pfTGroup10)))) (pfTJoin 352 160 171 (pfTJoin 352 64 96 (pfTJoin 352 32 32 pfTGroup11 pfTGroup12) (pfTJoin 416 32 64 pfTGroup13 (pfTJoin 448 32 32 pfTGroup14 pfTGroup15))) (pfTJoin 512 96 75 (pfTJoin 512 32 64 pfTGroup16 (pfTJoin 544 32 32 pfTGroup17 pfTGroup18)) (pfTJoin 608 32 43 pfTGroup19 (pfTJoin 640 32 11 pfTGroup20 pfTGroup21)))))
