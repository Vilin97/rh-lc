module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaNonsplitIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_nonsplit_isotropic_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (x : Fin d → E), x ≠ 0 → form σ W.J x x = 0 →
    ∀ (v : Pl (F := F)), IsEmpty (E →ₐ[F] Fv F v) → ∀ g ∈ UAt σ W (evFin F v),
      ∃ k ∈ KAt σ W v, ∃ t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, mat (g * k⁻¹) *ᵥ incV F x = t.1 • incV F x := by
  first | exact @GlobalTheory.InertLineTrans.exists_stab_line | exact GlobalTheory.InertLineTrans.exists_stab_line | (intros; apply GlobalTheory.InertLineTrans.exists_stab_line <;> assumption)
