module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalfStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointIntegralIffDualLatticeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPrimesSquarefreeConjugateIdealProdStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section
namespace GlobalTheory.AdjScalar
variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem map_adj_smul {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (σ : R →+* R) {m n : ℕ}
    (G1 : Matrix (Fin m) (Fin m) R) (G2 : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) K)
    (Q : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin m) R) (a : R) :
    P * ((G1 * ((a • X).map σ)ᵀ * G2).map f) * Q = f (σ a) • (P * ((G1 * (X.map σ)ᵀ * G2).map f) * Q) := by
  have h1 : (a • X).map σ = σ a • X.map σ := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ (M : Matrix (Fin m) (Fin n) R) (b : R), (b • M).map f = f b • M.map f := by
    intro M b; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a : AE D) (x : WO S T) :
    frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x :=
  map_adj_smul (toEAf D) (cA D) _ _ _ _ x a

theorem cA_incA' (c : D.host.E) : cA D (incA D c) = incA D (star c) := rfl

theorem smul_absorb {K : Type} [CommRing K] {m n : ℕ} (B : Matrix (Fin m) (Fin m) K) (F : Matrix (Fin m) (Fin n) K)
    (u v : K) (hF : u • F = F) : (u * v) • (B * F) = (1 : K) • (B * (v • F)) := by
  rw [one_smul, Matrix.mul_smul, mul_comm, mul_smul, ← Matrix.mul_smul B u F, hF]

theorem adjA_half_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (e : AE D) (c : D.host.E) (x : WO S T) (h : IsHalf (cA D e) x) :
    adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  have hx : cA D e • x = x := by
    ext i j; exact h i j
  have hF : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    conv_rhs => rw [← hx]
    rw [frMapAdj_smul, cA_cA]
  unfold adjA
  rw [frMapAdj_smul, cA_incA', map_one, map_mul]
  exact smul_absorb _ _ _ _ hF

end GlobalTheory.AdjScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel


theorem _root_.GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (c : D.host.E) (x : WO S T), IsHalf (cA D e) x → adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  first | exact @GlobalTheory.AdjScalar.adjA_half_smul | exact GlobalTheory.AdjScalar.adjA_half_smul | (intros; apply GlobalTheory.AdjScalar.adjA_half_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.HatScalar

theorem smul_mem_tens_of {E : Type} [Field E] [NumberField E] {n r : ℕ} {Λ : Lt E n} {L L' : Lt E r} (c : E)
    (h : ∀ u ∈ L, c • u ∈ L') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) :
    c • y ∈ tens Λ L' := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨v, hv, c • u, h u hu, ?_⟩
    rw [Matrix.vecMulVec_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem incA_smul_mem_hatA (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank)
    (c : D.host.E) (h : ∀ v ∈ L1, c • v ∈ L2) :
    ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  intro u hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, c • y, smul_mem_tens_of c h hy, ?_⟩
    ext a k
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E) c *
      _ = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.HatScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel


theorem _root_.GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup : ∀ (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) → ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  first | exact @GlobalTheory.HatScalar.incA_smul_mem_hatA | exact GlobalTheory.HatScalar.incA_smul_mem_hatA | (intros; apply GlobalTheory.HatScalar.incA_smul_mem_hatA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel



theorem exists_isGen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he
  have hS : S.gram = 1 := C.m.gS
  obtain ⟨γ, hγ, s, hs, h1, h2'⟩ := GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' D T.rank C.X.Λ ΛT hAA (Pg ∪ Q)
  obtain ⟨t, ht, hte⟩ := GlobalTheory.T.exists_integral_inverse_on_conjugate_half D (Pg ∪ Q) e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hecinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf : ∀ x : WO S T, IsHalf (cA D e) x → IsFinPt x := by
    intro x hx
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← hx i j, map_mul, hecinf, zero_mul]
  have hmulA : ∀ (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, ((s : D.host.E) * c) • v ∈ L2) →
      ∀ x : WO S T, IsHalf (cA D e) x → x ∈ hatA S T (tens (stdL D.host.E S.rank) L1) →
        incA D c • x ∈ hatA S T (tens (stdL D.host.E S.rank) L2) := by
    intro L1 L2 c hc x hx hxm
    have h3 := GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup D S T _ L1 L2 _ hc x hxm
    have h4 := smul_mem_hatA_of_int (fun o y hy => HatLat.smul_mem_tens _ _ o hy) ht h3
    convert h4 using 1
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    have hxij := hx i j
    calc incA D c * x i j = incA D c * (cA D e * x i j) := by rw [hxij]
      _ = (t * incA D (s : D.host.E) * cA D e) * (incA D c * x i j) := by rw [hte]; ring
      _ = t * (incA D (s : D.host.E) * incA D c * (cA D e * x i j)) := by ring
      _ = t * (incA D (s : D.host.E) * incA D c * x i j) := by rw [hxij]
  have hsc : ∀ (I : Ideal (𝓞 D.host.E)) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) →
      ∀ v ∈ I • L1, c • v ∈ I • L2 := by
    intro I L1 L2 c hc v hv
    refine Submodule.smul_induction_on hv (fun i hi w hw => ?_) (fun a b ha hb => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hi (hc w hw)
    · rw [smul_add]; exact add_mem ha hb
  refine ⟨e * incA D (star γ⁻¹), ⟨e * incA D (star γ), ?_⟩, ?_⟩
  · have hu : incA D (star γ⁻¹) * incA D (star γ) = 1 := by
      rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hγ), map_one]
    calc e * incA D (star γ⁻¹) * (e * incA D (star γ)) = (e * e) * (incA D (star γ⁻¹) * incA D (star γ)) :=
          mul_mul_mul_comm _ _ _ _
      _ = e := by rw [hu, mul_one, hee]
  intro x hx
  have hadj : adjA S T βS βT (e * incA D (star γ⁻¹)) x = adjA S T βS βT 1 (incA D γ⁻¹ • x) :=
    GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul D S T βS βT e γ⁻¹ x hx
  have hy : IsHalf (cA D e) (incA D γ⁻¹ • x) := by
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hx i j]
  have hyf := hinf _ hy
  have hback : incA D γ • (incA D γ⁻¹ • x) = x := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_smul]
  rw [hadj]
  obtain ⟨hsq, hle, hconj⟩ := GlobalTheory.T.prod_primes_squarefree_conjugateIdeal_prod D (Pg ∪ Q)
  have hmem : ∀ (I : Ideal (𝓞 D.host.E)),
      (incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • ΛT)) ↔
        x ∈ hatA S T (tens (stdL D.host.E S.rank) (I • C.X.Λ))) := by
    intro I
    constructor
    · intro hm
      have := hmulA (I • ΛT) (I • C.X.Λ) γ (hsc I ΛT C.X.Λ _ h2') _ hy hm
      rwa [hback] at this
    · intro hm
      exact hmulA (I • C.X.Λ) (I • ΛT) γ⁻¹ (hsc I C.X.Λ ΛT _ h1) x hx hm
  have hctop : conjI (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    unfold conjI
    exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp⟩
  constructor
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT ⊤ (by rw [← Ideal.one_eq_top]; exact squarefree_one) _ hyf
    rw [hctop, Submodule.top_smul] at hB
    have h5 := hmem ⊤
    rw [Submodule.top_smul, Submodule.top_smul] at h5
    rw [← h5, ← hB]
    constructor
    · intro h; exact ⟨h, fun PP hPP => absurd (top_le_iff.mp hPP) PP.isPrime.ne_top⟩
    · intro h; exact h.1
  · have hB := GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice D S T hS ΛT hsd βS βT hβT _ hsq _ hyf
    rw [hconj] at hB
    have hB' : (IsIntM (adjA S T βS βT 1 (incA D γ⁻¹ • x)) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E,
        (∏ PP ∈ Pg ∪ Q, PP.asIdeal) ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 (incA D γ⁻¹ • x)) = 0) ↔
        incA D γ⁻¹ • x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • ΛT)) := hB
    have h5 := hmem (liftI Pg Q)
    rw [← h5, ← hB']
    simp only [hle]

end GlobalTheory.LiftLevel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdeleGeneratesPolarisationIdealConjPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_idele_generates_polarisationIdeal_conjPlaces : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ a : AE D, (∃ b : AE D, a * b = e) ∧ GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a := by
  first | exact @GlobalTheory.LiftLevel.exists_isGen | exact GlobalTheory.LiftLevel.exists_isGen | (intros; apply GlobalTheory.LiftLevel.exists_isGen <;> assumption)
end
end
