module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumVectorIffLatticeEigen
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_vector_iff_lattice_eigen : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
    M.IsVac ψ v φ ↔ φ ∈ SB _ ∧ φ ≠ 0 ∧ ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 ∧ ∀ γ ∈ latAtV X W v,
      schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ =
        ψ (⅟(2 : AF F) * symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) • φ := by
  first | exact @GlobalTheory.VacLocEig.isVac_iff_loc | exact GlobalTheory.VacLocEig.isVac_iff_loc | (intros; apply GlobalTheory.VacLocEig.isVac_iff_loc <;> assumption)
