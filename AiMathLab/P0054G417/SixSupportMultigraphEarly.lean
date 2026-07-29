import AiMathLab.P0054G417.SixSupportMultigraphFinite

namespace AiMathLab.P0054.G417

set_option linter.style.longLine false
def sixEncodedMinimalSupportCovers : List Nat :=
  [
    22023, 21031, 20039, 21928, 20936, 19944, 21897, 18889, 17897, 20874, 18858, 16874,
    19851, 17835, 16843, 704577, 672833, 641089, 701537, 669793, 638049, 700545, 604289, 572545,
    667809, 603297, 539809, 635073, 570561, 538817, 701825, 670081, 638337, 704897, 673153, 641409,
    675201, 707969, 708993, 604577, 572833, 704929, 607649, 673185, 705953, 641441, 706977, 540097,
    606657, 672193, 704961, 673217, 641473, 674241, 573921, 639457, 704993, 640481, 673249, 641505,
    697442, 665698, 633954, 696450, 600194, 568450, 663714, 599202, 535714, 630978, 566466, 534722,
    697602, 665858, 634114, 704770, 673026, 641282, 675074, 707842, 708866, 600354, 568610, 704802,
    607522, 673058, 705826, 641314, 706850, 535874, 606530, 672066, 704834, 673090, 641346, 674114,
    573794, 639330, 704866, 640354, 673122, 641378, 695427, 501891, 470147, 662691, 500899, 437411,
    629955, 468163, 436419, 697571, 665827, 634083, 701667, 669923, 638179, 675043, 707811, 708835,
    502051, 470307, 701731, 506147, 669987, 702755, 638243, 703779, 437571, 505155, 668995, 701763,
    670019, 638275, 671043, 472419, 636259, 701795, 637283, 670051, 638307, 597156, 499876, 404644,
    564420, 467140, 403652, 696548, 600292, 568548, 700644, 604388, 572644, 607460, 705764, 706788,
    502020, 470276, 700676, 506116, 604420, 702724, 572676, 703748, 404804, 504132, 602436, 700740,
    604484, 572740, 605508, 471396, 569700, 700772, 571748, 604516, 572772, 531653, 434373, 402629,
    663781, 599269, 535781, 667877, 603365, 539877, 606437, 671973, 674021, 500997, 437509, 667909,
    505093, 603397, 668933, 539909, 670981, 404773, 504101, 602405, 667941, 603429, 539941, 605477,
    438629, 536933, 668005, 537957, 603493, 540005, 631014, 566502, 534758, 635110, 570598, 538854,
    573670, 639206, 640230, 468230, 436486, 635142, 472326, 570630, 636166, 538886, 637190, 403750,
    471334, 569638, 635174, 570662, 538918, 571686, 438598, 536902, 635206, 537926, 570694, 538950,
    697607, 665863, 634119, 675079, 707847, 708871, 600359, 568615, 607527, 705831, 706855, 535879,
    606535, 672071, 674119, 573799, 639335, 640359, 701831, 670087, 638343, 675207, 707975, 708999,
    604583, 572839, 607655, 705959, 706983, 540103, 606663, 672199, 674247, 573927, 639463, 640487,
    607751, 675335, 708135, 709191, 502056, 470312, 506152, 702760, 703784, 437576, 505160, 669000,
    671048, 472424, 636264, 637288, 704904, 673160, 641416, 675208, 707976, 709000, 506280, 604584,
    572840, 607656, 673192, 641448, 675240, 540104, 606664, 704968, 641480, 708040, 573928, 705000,
    673256, 709096, 404809, 504137, 602441, 605513, 471401, 569705, 571753, 506249, 670089, 638345,
    607625, 673161, 641417, 675209, 704937, 607657, 673193, 705961, 641449, 706985, 540105, 672201,
    704969, 673225, 705993, 639465, 705001, 641513, 707049, 438634, 536938, 537962, 505226, 701834,
    638346, 606602, 704906, 641418, 707978, 572842, 672170, 704938, 673194, 705962, 606666, 672202,
    704970, 673226, 641482, 674250, 640490, 673258, 641514, 674282, 472459, 701835, 670091, 573835,
    704907, 673163, 709003, 604587, 639403, 704939, 641451, 706987, 640459, 673227, 641483, 674251,
    573931, 639467, 705003, 640491, 673259, 641515, 22154305, 21138497, 20122689, 21597249, 22645825, 22678593,
    19042369, 18026561, 19435585, 22581313, 22614081, 16979009, 19403841, 21500993, 21566529, 18356289, 20453441, 20486209,
    19447873, 21610561, 22660161, 22693953, 15896673, 14880865, 16191585, 22483041, 22515809, 13833313, 16159841, 21402721,
    21468257, 15112289, 20355169, 20387937, 16200801, 21607521, 22657121, 22690913, 12784769, 16127105, 19272833, 19371137,
    15079553, 18225281, 18290817, 16199809, 19443841, 22591617, 22625409, 14031009, 17176737, 17209505, 16167073, 19411105,
    21509281, 21576865, 15118529, 18362561, 20460737, 20494529, 16201089, 19448193, 21610913, 22660545, 22694369, 11702370,
    10686562, 11866210, 22351970, 22384738, 9639010, 11834466, 21271650, 21337186, 10786914, 20224098, 20256866, 11871330,
    21603426, 22653026, 22686818, 8590466, 11801730, 19141762, 19240066, 10754178, 18094210, 18159746, 11870338, 19439746,
    22587522, 22621314, 9705634, 17045666, 17078434, 11837602, 19407010, 21505186, 21572770, 10789058, 18358466, 20456642,
    20490434, 11871490, 19448066, 21610786, 22660418, 22694242, 7541891, 11768963, 15963267, 16094339, 10721411, 14915715,
    15014019, 11869315, 16194691, 22489219, 22523011, 9672867, 13867171, 13932707, 11836579, 16161955, 21406883, 21474467,
    10788035, 15113411, 20358339, 20392131, 11871459, 16200931, 21607715, 22657347, 22691171, 8624292, 12818596, 12851364,
    11803812, 16129188, 19275940, 19377316, 10755268, 15080644, 18227396, 18294980, 11870436, 16199908, 19443972, 22591812,
    22625636, 9706693, 14032069, 17178821, 17212613, 11837669, 16167141, 19411205, 21509413, 21577061, 10789094, 15118566,
    18362630, 20460838, 20494662, 11871495, 16201095, 19448200, 21610921, 22660554, 22694379, 206703681
  ]

def sixSupportOrder4 : List Nat := [9, 10, 13, 14, 16, 17, 18, 19, 6, 7, 8, 11, 12, 15, 0, 1, 2, 3]

def sixCompletionGroups4 : List (List Nat) :=
  [
    [],
    [],
    [],
    [],
    [],
    [],
    [641482, 640490, 641514, 640459, 641483, 640491, 641515],
    [673226, 674250, 673258, 674282, 673227, 674251, 673259],
    [21031, 20039, 674119, 640359, 674247, 640487],
    [20936, 19944, 665863, 634119, 675079, 671048, 637288, 641480, 673256],
    [18889, 17897, 600359, 568615, 607527, 502056, 470312, 506152, 605513, 571753, 673225, 641513, 11871495],
    [20874, 19851, 670087, 638343, 675207, 673160, 641416, 675208, 404809, 504137, 602441, 471401, 569705, 506249, 670089, 638345, 607625, 673161, 641417, 675209, 638346, 641418, 670091, 673163],
    [18858, 17835, 604583, 572839, 607655, 437576, 505160, 669000, 472424, 636264, 506280, 604584, 572840, 607656, 673192, 641448, 675240, 607657, 673193, 641449, 438634, 505226, 572842, 673194, 472459, 604587, 641451, 16201095],
    [16874, 16843, 535879, 606535, 672071, 573799, 639335, 540103, 606663, 672199, 573927, 639463, 607751, 675335, 540104, 606664, 573928, 540105, 672201, 639465, 536938, 537962, 606602, 672170, 606666, 672202, 573835, 639403, 573931, 639467, 19448200, 21610921],
    [670081, 638337, 673153, 641409, 675201, 604577, 572833, 607649, 673185, 641441, 540097, 606657, 672193, 673217, 641473, 674241, 573921, 639457, 640481, 673249, 641505, 16201089, 19448193, 21610913],
    [672833, 641089, 665858, 634114, 673026, 641282, 675074, 600354, 568610, 607522, 673058, 641314, 535874, 606530, 672066, 673090, 641346, 674114, 573794, 639330, 640354, 673122, 641378, 19447873, 21610561, 11871490, 19448066, 21610786],
    [669793, 638049, 665698, 633954, 665827, 634083, 669923, 638179, 675043, 502051, 470307, 506147, 669987, 638243, 437571, 505155, 668995, 670019, 638275, 671043, 472419, 636259, 637283, 670051, 638307, 21597249, 16200801, 21607521, 11871330, 21603426, 11871459, 16200931, 21607715],
    [604289, 572545, 600194, 568450, 501891, 470147, 600292, 568548, 604388, 572644, 607460, 502020, 470276, 506116, 604420, 572676, 404804, 504132, 602436, 604484, 572740, 605508, 471396, 569700, 571748, 604516, 572772, 19435585, 16191585, 16199809, 19443841, 11866210, 11870338, 19439746, 11869315, 16194691, 11870436, 16199908, 19443972]
  ]

def sixCompletionStages4 : List (Option Nat) :=
  [
    none, some 8, some 8, none, some 9, some 9, none, some 10, some 10, some 11, some 12, some 13,
    some 11, some 12, some 13, none, some 15, some 15, none, some 16, some 16, none, some 17, some 17,
    none, none, none, none, none, none, none, some 14, some 14, none, some 14, some 14,
    some 14, none, none, some 14, some 14, none, some 14, some 14, none, some 14, none, some 14,
    some 14, some 14, none, some 14, some 14, some 14, some 14, some 14, none, some 14, some 14, some 14,
    none, some 16, some 16, none, some 17, some 17, none, none, none, none, none, none,
    none, some 15, some 15, none, some 15, some 15, some 15, none, none, some 15, some 15, none,
    some 15, some 15, none, some 15, none, some 15, some 15, some 15, none, some 15, some 15, some 15,
    some 15, some 15, none, some 15, some 15, some 15, none, some 17, some 17, none, none, none,
    none, none, none, none, some 16, some 16, none, some 16, some 16, some 16, none, none,
    some 16, some 16, none, some 16, some 16, none, some 16, none, some 16, some 16, some 16, none,
    some 16, some 16, some 16, some 16, some 16, none, some 16, some 16, some 16, none, none, none,
    none, none, none, none, some 17, some 17, none, some 17, some 17, some 17, none, none,
    some 17, some 17, none, some 17, some 17, none, some 17, none, some 17, some 17, some 17, none,
    some 17, some 17, some 17, some 17, some 17, none, some 17, some 17, some 17, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, some 9, some 9, some 9, none, none, some 10, some 10, some 10, none, none, some 13,
    some 13, some 13, some 8, some 13, some 13, some 8, none, some 11, some 11, some 11, none, none,
    some 12, some 12, some 12, none, none, some 13, some 13, some 13, some 8, some 13, some 13, some 8,
    some 13, some 13, none, none, some 10, some 10, some 10, none, none, some 12, some 12, some 12,
    some 9, some 12, some 12, some 9, none, some 11, some 11, some 11, none, none, some 12, some 12,
    some 12, some 12, some 12, some 12, some 12, some 13, some 13, none, some 9, none, some 13, none,
    some 9, none, some 11, some 11, some 11, some 10, some 11, some 11, some 10, some 11, some 11, some 11,
    some 11, some 11, some 11, some 11, none, some 12, some 12, none, some 12, none, some 13, some 13,
    none, some 10, none, some 13, none, some 10, none, some 12, some 13, some 13, some 12, none,
    some 11, some 13, none, some 11, none, some 12, some 13, none, some 12, none, some 13, some 13,
    none, some 7, some 6, some 7, some 6, some 7, some 6, some 7, some 12, none, some 11, some 13,
    none, some 11, none, some 12, some 13, none, some 12, none, some 6, some 7, some 6, some 7,
    some 13, some 13, none, some 6, some 7, some 6, none, none, none, some 16, none, none,
    none, none, some 17, none, none, none, none, none, none, none, none, none,
    some 15, some 15, none, none, none, none, some 17, none, none, none, none, none,
    none, none, none, none, some 16, some 16, none, none, none, none, none, none,
    none, none, none, some 17, some 17, none, none, none, none, none, none, none,
    none, none, none, none, none, none, some 14, some 14, some 14, none, none, none,
    none, some 17, none, none, none, none, none, none, none, none, none, some 16,
    some 16, none, none, none, none, none, none, none, none, none, some 17, some 17,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, some 15, some 15, some 15, none, none, none, none, none, none, none, none,
    none, some 17, some 17, none, none, none, none, none, none, none, none, none,
    none, none, none, none, some 16, some 16, some 16, none, none, none, none, none,
    none, none, none, none, none, none, none, none, some 17, some 17, some 17, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, some 10, some 12, some 13, some 13, none, none, none
  ]
def sixSupportOrder5 : List Nat := [10, 14, 17, 19, 20, 6, 7, 8, 9, 11, 12, 13, 15, 16, 18, 0, 1, 2, 3, 4]

def sixCompletionGroups5 : List (List Nat) :=
  [
    [],
    [],
    [],
    [],
    [22694379],
    [709191],
    [708871, 709096],
    [697607, 706855, 703784, 707049],
    [665863, 600359, 674119, 502056, 671048, 605513, 674282, 11871495],
    [21897, 20874, 708999, 709000, 404809, 504137, 602441, 709003],
    [21928, 18858, 701831, 706983, 437576, 505160, 669000, 706985, 438634, 505226, 701834, 701835, 706987],
    [20936, 18889, 670087, 604583, 674247, 470312, 506152, 702760, 472424, 506280, 604584, 471401, 506249, 670089, 674250, 472459, 670091, 604587, 674251, 16201095],
    [22023, 16874, 16843, 535879, 606535, 672071, 540103, 606663, 672199, 704904, 540104, 606664, 704968, 705000, 704937, 540105, 672201, 704969, 705001, 536938, 537962, 606602, 704906, 672170, 704938, 606666, 672202, 704970, 704907, 704939, 705003],
    [21031, 17897, 17835, 568615, 607527, 705831, 573799, 572839, 607655, 705959, 573927, 607751, 673160, 572840, 607656, 673192, 573928, 673256, 569705, 571753, 607625, 673161, 607657, 673193, 705961, 673225, 705993, 572842, 673194, 705962, 673226, 673258, 573835, 673163, 673227, 573931, 673259, 19448200],
    [20039, 19944, 19851, 634119, 675079, 707847, 639335, 640359, 638343, 675207, 707975, 639463, 640487, 675335, 708135, 636264, 637288, 641416, 675208, 707976, 641448, 675240, 641480, 708040, 638345, 641417, 675209, 641449, 639465, 641513, 638346, 641418, 707978, 641482, 640490, 641514, 639403, 641451, 640459, 641483, 639467, 640491, 641515, 21610921, 22660554],
    [701825, 670081, 638337, 704897, 673153, 641409, 675201, 707969, 708993, 604577, 572833, 704929, 607649, 673185, 705953, 641441, 706977, 540097, 606657, 672193, 704961, 673217, 641473, 674241, 573921, 639457, 704993, 640481, 673249, 641505, 16201089, 19448193, 21610913, 22660545, 22694369],
    [704577, 672833, 641089, 697602, 665858, 634114, 704770, 673026, 641282, 675074, 707842, 708866, 600354, 568610, 704802, 607522, 673058, 705826, 641314, 706850, 535874, 606530, 672066, 704834, 673090, 641346, 674114, 573794, 639330, 704866, 640354, 673122, 641378, 19447873, 21610561, 22660161, 22693953, 11871490, 19448066, 21610786, 22660418, 22694242],
    [701537, 669793, 638049, 697442, 665698, 633954, 697571, 665827, 634083, 701667, 669923, 638179, 675043, 707811, 708835, 502051, 470307, 701731, 506147, 669987, 702755, 638243, 703779, 437571, 505155, 668995, 701763, 670019, 638275, 671043, 472419, 636259, 701795, 637283, 670051, 638307, 21597249, 22645825, 22678593, 16200801, 21607521, 22657121, 22690913, 11871330, 21603426, 22653026, 22686818, 11871459, 16200931, 21607715, 22657347, 22691171],
    [700545, 604289, 572545, 696450, 600194, 568450, 695427, 501891, 470147, 696548, 600292, 568548, 700644, 604388, 572644, 607460, 705764, 706788, 502020, 470276, 700676, 506116, 604420, 702724, 572676, 703748, 404804, 504132, 602436, 700740, 604484, 572740, 605508, 471396, 569700, 700772, 571748, 604516, 572772, 22154305, 19435585, 22581313, 22614081, 16191585, 22483041, 22515809, 16199809, 19443841, 22591617, 22625409, 11866210, 22351970, 22384738, 11870338, 19439746, 22587522, 22621314, 11869315, 16194691, 22489219, 22523011, 11870436, 16199908, 19443972, 22591812, 22625636],
    [667809, 603297, 539809, 663714, 599202, 535714, 662691, 500899, 437411, 597156, 499876, 404644, 663781, 599269, 535781, 667877, 603365, 539877, 606437, 671973, 674021, 500997, 437509, 667909, 505093, 603397, 668933, 539909, 670981, 404773, 504101, 602405, 667941, 603429, 539941, 605477, 438629, 536933, 668005, 537957, 603493, 540005, 21138497, 19042369, 19403841, 21500993, 21566529, 15896673, 16159841, 21402721, 21468257, 16127105, 19272833, 19371137, 16167073, 19411105, 21509281, 21576865, 11702370, 11834466, 21271650, 21337186, 11801730, 19141762, 19240066, 11837602, 19407010, 21505186, 21572770, 11768963, 15963267, 16094339, 11836579, 16161955, 21406883, 21474467, 11803812, 16129188, 19275940, 19377316, 11837669, 16167141, 19411205, 21509413, 21577061]
  ]

def sixCompletionStages5 : List (Option Nat) :=
  [
    some 12, some 13, some 14, some 10, some 11, some 14, some 9, some 11, some 13, some 9, some 10, some 12,
    some 14, some 13, some 12, some 16, some 16, some 16, some 17, some 17, some 17, some 18, some 18, some 18,
    some 19, some 19, some 19, none, none, none, some 15, some 15, some 15, some 15, some 15, some 15,
    some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15,
    some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15, some 15,
    some 17, some 17, some 17, some 18, some 18, some 18, some 19, some 19, some 19, none, none, none,
    some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16,
    some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16, some 16,
    some 16, some 16, some 16, some 16, some 16, some 16, some 18, some 18, some 18, some 19, some 19, some 19,
    none, none, none, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17,
    some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17,
    some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 17, some 19, some 19, some 19,
    none, none, none, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18,
    some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18,
    some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, some 18, none, none, none,
    some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19,
    some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19,
    some 19, some 19, some 19, some 19, some 19, some 19, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none,
    some 7, some 8, some 14, some 14, some 14, some 6, some 8, some 13, some 13, some 13, some 7, some 12,
    some 12, some 12, some 8, some 13, some 14, some 14, some 10, some 11, some 14, some 14, some 14, some 9,
    some 11, some 13, some 13, some 13, some 10, some 12, some 12, some 12, some 11, some 13, some 14, some 14,
    some 13, some 14, some 14, some 5, some 8, some 11, some 11, some 11, some 7, some 10, some 10, some 10,
    some 8, some 11, some 14, some 14, some 12, some 13, some 14, some 14, some 14, some 9, some 11, some 11,
    some 13, some 13, some 13, some 14, some 14, some 12, some 12, some 12, some 14, some 14, some 13, some 12,
    some 13, some 6, some 9, some 9, some 9, some 8, some 11, some 13, some 13, some 11, some 11, some 14,
    some 13, some 13, some 14, some 14, some 12, some 13, some 13, some 13, some 14, some 10, some 12, some 12,
    some 12, some 13, some 13, some 14, some 12, some 14, some 7, some 10, some 12, some 12, some 10, some 10,
    some 14, some 12, some 12, some 14, some 14, some 13, some 12, some 12, some 13, some 13, some 12, some 12,
    some 12, some 13, some 14, some 11, some 14, some 13, some 14, some 8, some 11, some 10, some 11, some 13,
    some 12, some 13, some 9, some 11, some 14, some 12, some 14, some 10, some 14, some 13, some 14, some 11,
    some 13, some 14, some 12, some 14, some 13, some 14, some 18, some 19, none, some 17, some 17, some 17,
    some 19, none, some 18, some 18, some 18, none, some 19, some 19, some 19, none, none, none,
    some 16, some 16, some 16, some 16, some 19, none, some 18, some 18, some 18, none, some 19, some 19,
    some 19, none, none, none, some 17, some 17, some 17, some 17, none, some 19, some 19, some 19,
    none, none, none, some 18, some 18, some 18, some 18, none, none, none, some 19, some 19,
    some 19, some 19, none, none, none, none, some 15, some 15, some 15, some 15, some 15, some 19,
    none, some 18, some 18, some 18, none, some 19, some 19, some 19, none, none, none, some 17,
    some 17, some 17, some 17, none, some 19, some 19, some 19, none, none, none, some 18, some 18,
    some 18, some 18, none, none, none, some 19, some 19, some 19, some 19, none, none, none,
    none, some 16, some 16, some 16, some 16, some 16, none, some 19, some 19, some 19, none, none,
    none, some 18, some 18, some 18, some 18, none, none, none, some 19, some 19, some 19, some 19,
    none, none, none, none, some 17, some 17, some 17, some 17, some 17, none, none, none,
    some 19, some 19, some 19, some 19, none, none, none, none, some 18, some 18, some 18, some 18,
    some 18, none, none, none, none, some 19, some 19, some 19, some 19, some 19, none, none,
    none, none, none, some 8, some 11, some 13, some 14, some 14, some 4, none
  ]
def sixSupportOrder6 : List Nat := [0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 15, 16, 17, 2, 18, 19, 3, 20, 4, 5]

def sixCompletionGroups6 : List (List Nat) :=
  [
    [],
    [],
    [],
    [],
    [],
    [11871495],
    [404809],
    [437576, 438634],
    [470312, 472424, 471401, 472459],
    [502056, 506152, 505160, 506280, 504137, 506249, 505226, 16201089, 16201095],
    [11871490],
    [16874, 16843, 540097, 535874, 535879, 540103, 540104, 540105, 536938, 537962],
    [17897, 17835, 572833, 573921, 568610, 573794, 568615, 573799, 572839, 573927, 572840, 573928, 569705, 571753, 572842, 573835, 573931],
    [18889, 18858, 604577, 607649, 606657, 600354, 607522, 606530, 600359, 607527, 606535, 604583, 607655, 606663, 607751, 604584, 607656, 606664, 602441, 605513, 607625, 607657, 606602, 606666, 604587, 19447873, 19448193, 19448066, 19448200],
    [502051, 470307, 506147, 437571, 505155, 472419, 16200801, 11871330, 11871459, 16200931],
    [20039, 19944, 19851, 641089, 638049, 638337, 641409, 641441, 641473, 639457, 640481, 641505, 633954, 634114, 641282, 641314, 641346, 639330, 640354, 641378, 634083, 638179, 638243, 638275, 636259, 637283, 638307, 634119, 639335, 640359, 638343, 639463, 640487, 636264, 637288, 641416, 641448, 641480, 638345, 641417, 641449, 639465, 641513, 638346, 641418, 641482, 640490, 641514, 639403, 641451, 640459, 641483, 639467, 640491, 641515],
    [21031, 20936, 20874, 672833, 669793, 670081, 673153, 675201, 673185, 672193, 673217, 674241, 673249, 665698, 665858, 673026, 675074, 673058, 672066, 673090, 674114, 673122, 665827, 669923, 675043, 669987, 668995, 670019, 671043, 670051, 665863, 675079, 672071, 674119, 670087, 675207, 672199, 674247, 675335, 669000, 671048, 673160, 675208, 673192, 675240, 673256, 670089, 673161, 675209, 673193, 672201, 673225, 672170, 673194, 672202, 673226, 674250, 673258, 674282, 670091, 673163, 673227, 674251, 673259, 21597249, 21610561, 21607521, 21610913, 21603426, 21610786, 21607715, 21610921],
    [604289, 572545, 600194, 568450, 501891, 470147, 600292, 568548, 604388, 572644, 607460, 502020, 470276, 506116, 604420, 572676, 404804, 504132, 602436, 604484, 572740, 605508, 471396, 569700, 571748, 604516, 572772, 19435585, 16191585, 16199809, 19443841, 11866210, 11870338, 19439746, 11869315, 16194691, 11870436, 16199908, 19443972],
    [22023, 21928, 21897, 704577, 701537, 700545, 701825, 704897, 707969, 708993, 704929, 705953, 706977, 704961, 704993, 697442, 696450, 697602, 704770, 707842, 708866, 704802, 705826, 706850, 704834, 704866, 695427, 697571, 701667, 707811, 708835, 701731, 702755, 703779, 701763, 701795, 696548, 700644, 705764, 706788, 700676, 702724, 703748, 700740, 700772, 697607, 707847, 708871, 705831, 706855, 701831, 707975, 708999, 705959, 706983, 708135, 709191, 702760, 703784, 704904, 707976, 709000, 704968, 708040, 705000, 709096, 704937, 705961, 706985, 704969, 705993, 705001, 707049, 701834, 704906, 707978, 704938, 705962, 704970, 701835, 704907, 709003, 704939, 706987, 705003, 22154305, 22645825, 22678593, 22581313, 22614081, 22660161, 22693953, 22483041, 22515809, 22657121, 22690913, 22591617, 22625409, 22660545, 22694369, 22351970, 22384738, 22653026, 22686818, 22587522, 22621314, 22660418, 22694242, 22489219, 22523011, 22657347, 22691171, 22591812, 22625636, 22660554, 22694379],
    [667809, 603297, 539809, 663714, 599202, 535714, 662691, 500899, 437411, 597156, 499876, 404644, 663781, 599269, 535781, 667877, 603365, 539877, 606437, 671973, 674021, 500997, 437509, 667909, 505093, 603397, 668933, 539909, 670981, 404773, 504101, 602405, 667941, 603429, 539941, 605477, 438629, 536933, 668005, 537957, 603493, 540005, 21138497, 19042369, 19403841, 21500993, 21566529, 15896673, 16159841, 21402721, 21468257, 16127105, 19272833, 19371137, 16167073, 19411105, 21509281, 21576865, 11702370, 11834466, 21271650, 21337186, 11801730, 19141762, 19240066, 11837602, 19407010, 21505186, 21572770, 11768963, 15963267, 16094339, 11836579, 16161955, 21406883, 21474467, 11803812, 16129188, 19275940, 19377316, 11837669, 16167141, 19411205, 21509413, 21577061],
    [635073, 570561, 538817, 630978, 566466, 534722, 629955, 468163, 436419, 564420, 467140, 403652, 531653, 434373, 402629, 631014, 566502, 534758, 635110, 570598, 538854, 573670, 639206, 640230, 468230, 436486, 635142, 472326, 570630, 636166, 538886, 637190, 403750, 471334, 569638, 635174, 570662, 538918, 571686, 438598, 536902, 635206, 537926, 570694, 538950, 20122689, 18026561, 16979009, 18356289, 20453441, 20486209, 14880865, 13833313, 15112289, 20355169, 20387937, 12784769, 15079553, 18225281, 18290817, 14031009, 17176737, 17209505, 15118529, 18362561, 20460737, 20494529, 10686562, 9639010, 10786914, 20224098, 20256866, 8590466, 10754178, 18094210, 18159746, 9705634, 17045666, 17078434, 10789058, 18358466, 20456642, 20490434, 7541891, 10721411, 14915715, 15014019, 9672867, 13867171, 13932707, 10788035, 15113411, 20358339, 20392131, 8624292, 12818596, 12851364, 10755268, 15080644, 18227396, 18294980, 9706693, 14032069, 17178821, 17212613, 10789094, 15118566, 18362630, 20460838, 20494662, 206703681]
  ]

def sixCompletionStages6 : List (Option Nat) :=
  [
    some 18, some 16, some 15, some 18, some 16, some 15, some 18, some 13, some 12, some 16, some 13, some 11,
    some 15, some 12, some 11, some 18, some 16, some 15, some 18, some 16, some 15, some 18, some 17, some 17,
    some 19, some 19, some 19, some 20, some 20, some 20, some 18, some 16, some 15, some 18, some 16, some 15,
    some 16, some 18, some 18, some 13, some 12, some 18, some 13, some 16, some 18, some 15, some 18, some 11,
    some 13, some 16, some 18, some 16, some 15, some 16, some 12, some 15, some 18, some 15, some 16, some 15,
    some 18, some 16, some 15, some 18, some 17, some 17, some 19, some 19, some 19, some 20, some 20, some 20,
    some 18, some 16, some 15, some 18, some 16, some 15, some 16, some 18, some 18, some 13, some 12, some 18,
    some 13, some 16, some 18, some 15, some 18, some 11, some 13, some 16, some 18, some 16, some 15, some 16,
    some 12, some 15, some 18, some 15, some 16, some 15, some 18, some 17, some 17, some 19, some 19, some 19,
    some 20, some 20, some 20, some 18, some 16, some 15, some 18, some 16, some 15, some 16, some 18, some 18,
    some 14, some 14, some 18, some 14, some 16, some 18, some 15, some 18, some 14, some 14, some 16, some 18,
    some 16, some 15, some 16, some 14, some 15, some 18, some 15, some 16, some 15, some 19, some 19, some 19,
    some 20, some 20, some 20, some 18, some 17, some 17, some 18, some 17, some 17, some 17, some 18, some 18,
    some 17, some 17, some 18, some 17, some 17, some 18, some 17, some 18, some 17, some 17, some 17, some 18,
    some 17, some 17, some 17, some 17, some 17, some 18, some 17, some 17, some 17, some 20, some 20, some 20,
    some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19,
    some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19, some 19,
    some 19, some 19, some 19, some 19, some 19, some 19, some 20, some 20, some 20, some 20, some 20, some 20,
    some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20,
    some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20, some 20,
    some 18, some 16, some 15, some 16, some 18, some 18, some 13, some 12, some 13, some 18, some 18, some 11,
    some 13, some 16, some 16, some 12, some 15, some 15, some 18, some 16, some 15, some 16, some 18, some 18,
    some 13, some 12, some 13, some 18, some 18, some 11, some 13, some 16, some 16, some 12, some 15, some 15,
    some 13, some 16, some 18, some 18, some 9, some 8, some 9, some 18, some 18, some 7, some 9, some 16,
    some 16, some 8, some 15, some 15, some 18, some 16, some 15, some 16, some 18, some 18, some 9, some 13,
    some 12, some 13, some 16, some 15, some 16, some 11, some 13, some 18, some 15, some 18, some 12, some 18,
    some 16, some 18, some 6, some 9, some 13, some 13, some 8, some 12, some 12, some 9, some 16, some 15,
    some 13, some 16, some 15, some 16, some 18, some 13, some 16, some 18, some 15, some 18, some 11, some 16,
    some 18, some 16, some 18, some 15, some 18, some 15, some 18, some 7, some 11, some 11, some 9, some 18,
    some 15, some 13, some 18, some 15, some 18, some 12, some 16, some 18, some 16, some 18, some 13, some 16,
    some 18, some 16, some 15, some 16, some 15, some 16, some 15, some 16, some 8, some 18, some 16, some 12,
    some 18, some 16, some 18, some 13, some 15, some 18, some 15, some 18, some 15, some 16, some 15, some 16,
    some 12, some 15, some 18, some 15, some 16, some 15, some 18, some 19, some 20, some 16, some 18, some 18,
    some 19, some 20, some 17, some 18, some 18, some 20, some 19, some 19, some 19, some 20, some 20, some 20,
    some 13, some 16, some 18, some 18, some 19, some 20, some 17, some 18, some 18, some 20, some 19, some 19,
    some 19, some 20, some 20, some 20, some 14, some 16, some 18, some 18, some 20, some 19, some 19, some 19,
    some 20, some 20, some 20, some 17, some 17, some 18, some 18, some 20, some 20, some 20, some 19, some 19,
    some 19, some 19, some 20, some 20, some 20, some 20, some 9, some 13, some 16, some 18, some 18, some 19,
    some 20, some 17, some 18, some 18, some 20, some 19, some 19, some 19, some 20, some 20, some 20, some 14,
    some 16, some 18, some 18, some 20, some 19, some 19, some 19, some 20, some 20, some 20, some 17, some 17,
    some 18, some 18, some 20, some 20, some 20, some 19, some 19, some 19, some 19, some 20, some 20, some 20,
    some 20, some 10, some 13, some 16, some 18, some 18, some 20, some 19, some 19, some 19, some 20, some 20,
    some 20, some 17, some 17, some 18, some 18, some 20, some 20, some 20, some 19, some 19, some 19, some 19,
    some 20, some 20, some 20, some 20, some 14, some 14, some 16, some 18, some 18, some 20, some 20, some 20,
    some 19, some 19, some 19, some 19, some 20, some 20, some 20, some 20, some 17, some 17, some 17, some 18,
    some 18, some 20, some 20, some 20, some 20, some 19, some 19, some 19, some 19, some 19, some 20, some 20,
    some 20, some 20, some 20, some 5, some 9, some 13, some 16, some 18, some 18, some 20
  ]

def sixCompactMultiplicityWeight : Nat → Nat
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 64
  | 4 => 256
  | 5 => 1024
  | 6 => 4096
  | 7 => 16384
  | 8 => 65536
  | 9 => 262144
  | 10 => 1048576
  | 11 => 4194304
  | 12 => 16777216
  | 13 => 67108864
  | 14 => 268435456
  | 15 => 1073741824
  | 16 => 4294967296
  | 17 => 17179869184
  | 18 => 68719476736
  | 19 => 274877906944
  | 20 => 1099511627776
  | _ => 0

def sixCompactMultiplicityDigit (m s : Nat) : Nat :=
  Nat.land (Nat.shiftRight m (2 * s)) 3

def sixCompactSetMultiplicity (m s k : Nat) : Nat :=
  m + k * sixCompactMultiplicityWeight s

structure SixCompactDegrees where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  d4 : Nat
  d5 : Nat
  deriving DecidableEq

def sixCompactDegreesZero : SixCompactDegrees := ⟨0, 0, 0, 0, 0, 0⟩

def sixCompactDegree (degrees : SixCompactDegrees) : Nat → Nat
  | 0 => degrees.d0
  | 1 => degrees.d1
  | 2 => degrees.d2
  | 3 => degrees.d3
  | 4 => degrees.d4
  | 5 => degrees.d5
  | _ => 0

def sixCompactAddSupportDegree
    (degrees : SixCompactDegrees) (s k : Nat) : SixCompactDegrees :=
  match s with
  | 0 => { degrees with d0 := degrees.d0 + k }
  | 1 => { degrees with d1 := degrees.d1 + k }
  | 2 => { degrees with d2 := degrees.d2 + k }
  | 3 => { degrees with d3 := degrees.d3 + k }
  | 4 => { degrees with d4 := degrees.d4 + k }
  | 5 => { degrees with d5 := degrees.d5 + k }
  | 6 => { degrees with d0 := degrees.d0 + k, d1 := degrees.d1 + k }
  | 7 => { degrees with d0 := degrees.d0 + k, d2 := degrees.d2 + k }
  | 8 => { degrees with d0 := degrees.d0 + k, d3 := degrees.d3 + k }
  | 9 => { degrees with d0 := degrees.d0 + k, d4 := degrees.d4 + k }
  | 10 => { degrees with d0 := degrees.d0 + k, d5 := degrees.d5 + k }
  | 11 => { degrees with d1 := degrees.d1 + k, d2 := degrees.d2 + k }
  | 12 => { degrees with d1 := degrees.d1 + k, d3 := degrees.d3 + k }
  | 13 => { degrees with d1 := degrees.d1 + k, d4 := degrees.d4 + k }
  | 14 => { degrees with d1 := degrees.d1 + k, d5 := degrees.d5 + k }
  | 15 => { degrees with d2 := degrees.d2 + k, d3 := degrees.d3 + k }
  | 16 => { degrees with d2 := degrees.d2 + k, d4 := degrees.d4 + k }
  | 17 => { degrees with d2 := degrees.d2 + k, d5 := degrees.d5 + k }
  | 18 => { degrees with d3 := degrees.d3 + k, d4 := degrees.d4 + k }
  | 19 => { degrees with d3 := degrees.d3 + k, d5 := degrees.d5 + k }
  | 20 => { degrees with d4 := degrees.d4 + k, d5 := degrees.d5 + k }
  | _ => degrees

def sixCompactCoverSlotValue (m slot : Nat) : Nat :=
  if slot = 0 then 1 else sixCompactMultiplicityDigit m (slot - 1)

def sixCompactCoverValue (m code : Nat) : Nat :=
  sixCompactCoverSlotValue m (Nat.land code 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 5) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 10) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 15) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 20) 31) *
    sixCompactCoverSlotValue m (Nat.land (Nat.shiftRight code 25) 31)

def sixCompactCoverGroupValue (m : Nat) (group : List Nat) : Nat :=
  (group.map fun code ↦ sixCompactCoverValue m code).sum

def sixRemainingCapacity (supports : List Nat) (v : Nat) : Nat :=
  3 * (supports.filter fun s ↦ sixSupportContains s v).length

def sixCompactDegreeStateValidBool
    (lowCount : Nat) (degrees : SixCompactDegrees) : Bool :=
  (List.range 6).all fun v ↦
    if v < lowCount then decide (sixCompactDegree degrees v = 3)
    else decide (4 ≤ sixCompactDegree degrees v)

def sixCompactMultiplicityChoices
    (lowCount : Nat) (degrees : SixCompactDegrees) (s : Nat) : List Nat :=
  (List.range 4).filter fun k ↦
    (decide (k = 0) || sixSupportTouchesLowBool lowCount s) &&
      (List.range lowCount).all fun v ↦
        !sixSupportContains s v || decide (sixCompactDegree degrees v + k ≤ 3)

def sixCompactDegreeCompletionPossibleBool
    (lowCount : Nat) (supports : List Nat) (degrees : SixCompactDegrees) : Bool :=
  (List.range 6).all fun v ↦
    let target := if v < lowCount then 3 else 4
    decide (target ≤ sixCompactDegree degrees v + sixRemainingCapacity supports v)

def sixSupportMultigraphEarlyCheckAux
    (lowCount minimum : Nat) : List Nat → List (List Nat) →
      Nat → SixCompactDegrees → Nat → Bool
  | [], [], _, degrees, count =>
      if sixCompactDegreeStateValidBool lowCount degrees then decide (minimum ≤ count) else true
  | s :: supports, group :: groups, m, degrees, count =>
      (sixCompactMultiplicityChoices lowCount degrees s).all fun k ↦
        let nextM := sixCompactSetMultiplicity m s k
        let nextDegrees := sixCompactAddSupportDegree degrees s k
        let nextCount := count + sixCompactCoverGroupValue nextM group
        decide (minimum ≤ nextCount) ||
          !sixCompactDegreeCompletionPossibleBool lowCount supports nextDegrees ||
          sixSupportMultigraphEarlyCheckAux lowCount minimum supports groups
            nextM nextDegrees nextCount
  | _, _, _, _, _ => false

def sixSupportMultigraphEarlyCheck (lowCount : Nat) : Bool :=
  match lowCount with
  | 4 => sixSupportMultigraphEarlyCheckAux 4 15 sixSupportOrder4 sixCompletionGroups4
      0 sixCompactDegreesZero 0
  | 5 => sixSupportMultigraphEarlyCheckAux 5 15 sixSupportOrder5 sixCompletionGroups5
      0 sixCompactDegreesZero 0
  | 6 => sixSupportMultigraphEarlyCheckAux 6 15 sixSupportOrder6 sixCompletionGroups6
      0 sixCompactDegreesZero 0
  | _ => false

def sixSupportMultigraphEarlySubcheckTwo (lowCount a b : Nat) : Bool :=
  let data := match lowCount with
    | 4 => some (sixSupportOrder4, sixCompletionGroups4)
    | 5 => some (sixSupportOrder5, sixCompletionGroups5)
    | 6 => some (sixSupportOrder6, sixCompletionGroups6)
    | _ => none
  match data with
  | some (s0 :: s1 :: supports, group0 :: group1 :: groups) =>
      let m0 := sixCompactSetMultiplicity 0 s0 a
      let degrees0 := sixCompactAddSupportDegree sixCompactDegreesZero s0 a
      let count0 := sixCompactCoverGroupValue m0 group0
      let m1 := sixCompactSetMultiplicity m0 s1 b
      let degrees1 := sixCompactAddSupportDegree degrees0 s1 b
      let count1 := count0 + sixCompactCoverGroupValue m1 group1
      decide (15 ≤ count1) ||
        !sixCompactDegreeCompletionPossibleBool lowCount supports degrees1 ||
        sixSupportMultigraphEarlyCheckAux lowCount 15 supports groups m1 degrees1 count1
  | _ => false

end AiMathLab.P0054.G417
