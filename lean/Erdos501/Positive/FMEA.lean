import Erdos501.External.ElementarySectionBound
import Erdos501.Positive.RecursiveConstruction

namespace Erdos501

theorem fmea_implies_StrongP_of_key_selection
    (hKey : ∀ ν : FullMeasureExtension, KeySelectionPrinciple ν) :
    FMEA → StrongP := by
  rintro ⟨ν⟩
  exact strongP_of_key_selection ν (hKey ν)

theorem fmea_implies_P_of_key_selection
    (hKey : ∀ ν : FullMeasureExtension, KeySelectionPrinciple ν) :
    FMEA → P := by
  intro hFMEA
  exact StrongP.implies_P (fmea_implies_StrongP_of_key_selection hKey hFMEA)

theorem fmea_implies_StrongP : FMEA → StrongP :=
  fmea_implies_StrongP_of_key_selection
    (fun ν => keySelection_of_sectionBound ν (ElementarySectionBound.elementary_section_bound ν))

theorem fmea_implies_P : FMEA → P :=
  fun hFMEA => StrongP.implies_P (fmea_implies_StrongP hFMEA)

end Erdos501
