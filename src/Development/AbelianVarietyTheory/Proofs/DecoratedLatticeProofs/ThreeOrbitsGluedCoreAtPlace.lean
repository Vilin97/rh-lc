module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCasesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.GluedInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec' (p : SplitPt D k) {S : HSp D} (h : GA D S) (u : Fin S.rank → k) :
    mt S h *ᵥ (fun i => p.sec (u i)) = fun i => p.sec (((mt S h).map p.pr *ᵥ u) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec]

theorem cAe_smul (p : SplitPt D k) {r : ℕ} (z : Fin r → AE D) :
    cA D p.e • z = fun i => cA D (p.sec (p.pr (cA D (z i)))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, p.sec_pr, map_mul, cA_cA]

def form (p : SplitPt D k) (S : HSp D) (x w : Fin S.rank → k) : k :=
  ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * w j

theorem form_eq (p : SplitPt D k) (S : HSp D) (x : Fin S.rank → k) (c : Fin S.rank → D.host.E) :
    form p S x (fun j => p.pr (cA D (incA D (c j)))) =
      x ⬝ᵥ fun i => p.pr (incA D ((star (S.gram *ᵥ c)) i)) := by
  unfold form
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1

  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, map_sum, star_mul', map_mul]
  rfl

theorem row_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    star (S.gram *ᵥ vecB o ζ) ᵥ* o.iA = 0 ∧ star (S.gram *ᵥ vecB o ζ) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
  have hr : star (S.gram *ᵥ vecB o ζ) = star ζ ᵥ* (o.iBᴴ * S.gram) := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, gram_conjTranspose]
  rw [hr]
  constructor
  · rw [Matrix.vecMul_vecMul, o.orth, Matrix.vecMul_zero]
  · rw [vecB, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem form_frame (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (hs : IsSumFrame B.o B.ζ β β₀) (y : n ⊕ Fin 1 → k) :
    form p B.V₀ (β₀.b *ᵥ y) (fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j))) =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := by
  obtain ⟨h1, h2⟩ := row_orth B.o B.ζ
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  set r := star (B.V₀.gram *ᵥ vecB B.o B.ζ) with hr
  change form p B.V₀ _ (fun j => p.pr (cA D (incA D (vecB B.o B.ζ j)))) = _
  rw [form_eq, ← hr, hs, Matrix.fromCols_mulVec, add_dotProduct]
  have hA : (⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) = 0 := by
    funext a
    have hm : B.o.jA.map p.pr = B.o.iA.map ι := by
      rw [OrthDec.jA, rat, Matrix.map_map]; rfl
    rw [hm, ← RingHom.map_vecMul, h1]
    simp
  have e1 : ((B.o.jA.map p.pr * β.b) *ᵥ (y ∘ Sum.inl)) ⬝ᵥ (fun i => p.pr (incA D (r i))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
    change ((⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) ᵥ* β.b) ⬝ᵥ _ = 0
    rw [hA, Matrix.zero_vecMul, zero_dotProduct]
  have e2 : (replicateCol (Fin 1) (fun i => p.pr (ratV (vecB B.o B.ζ) i)) *ᵥ (y ∘ Sum.inr)) =
      y (Sum.inr 0) • (⇑ι ∘ vecB B.o B.ζ) := by
    funext i
    simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm, ratV, hι]
  rw [e1, zero_add, e2, smul_dotProduct, smul_eq_mul, mul_comm]
  congr 1
  change (⇑ι ∘ vecB B.o B.ζ) ⬝ᵥ (⇑ι ∘ r) = ι _
  rw [← RingHom.map_dotProduct, dotProduct_comm, h2]

end GlobalTheory.FinPl.GluedInt


open GlobalTheory.FinPl.GluedInt in
theorem GlobalTheory.FinPl.glued_last_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ _ hyp x hx
  have hu := hg.unit.2 B.V₀ L₀
  have hz := cAe_smul p (ratV (vecB B.o B.ζ))
  set zk : Fin B.V₀.rank → k := fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j)) with hzk
  have hN : ∀ y : n ⊕ Fin 1 → k, form p B.V₀ (β₀.b *ᵥ y) zk =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := form_frame p B β β₀ hg.sum
  have hvN := hg.norm
  set N := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) with hNdef
  have hq0 : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact q.ne_zero
  have hmem : (fun i => cA D (p.sec (zk i))) ∈ latV B.V₀ L₀ (· = p.v) := by
    rw [FrameLat.csec_mem_iff hsd]
    intro x' hx'
    have hb : β₀.b *ᵥ (β₀.b' *ᵥ x') = x' := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    have hy : β₀.b' *ᵥ x' ∈ gluedS q 1 P.ker P.vec := (hg.lat _).2 (by rw [hb]; exact hx')
    rw [← gluedLat_one, mem_gluedLat] at hy
    obtain ⟨s, -, hs⟩ := hy
    have h0 := (hs 0).2.1 rfl
    change form p B.V₀ x' zk ∈ 𝒪[k]
    rw [← hb, hN, h0, Valuation.mem_integer_iff, map_mul, map_mul, hvN, Unif.inv, map_inv₀, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul]
    exact s.2
  have hA : cA D p.e • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by rw [hu, hz]; exact hmem
  have h1 := hyp (cA D p.e) hA
  rw [hu, hz, FrameLat.mt_csec] at h1
  rw [mt_sec' p] at hx
  have h2 := (FrameLat.csec_mem_iff hsd _).1 h1 _ hx
  rw [FrameLat.pairing_inv] at h2
  change form p B.V₀ (β₀.b *ᵥ x) zk ∈ 𝒪[k] at h2
  rw [hN, Valuation.mem_integer_iff, map_mul, hvN] at h2
  rw [Valuation.mem_integer_iff, map_mul]
  exact h2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedSplitPlaceLineCoordinateIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)

theorem _root_.GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.glued_last_integral | exact GlobalTheory.FinPl.glued_last_integral | (intros; apply GlobalTheory.FinPl.glued_last_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
namespace GlobalTheory.FinPl

theorem emb_map_eq_one {D : D7} {S A L : HSp D} (o : OrthDec S A L) {R : Type} [CommRing R] (f : AE D →+* R)
    {a : GA D A} (ha : (Formalism.L2.Theta.mt A a).map f = 1) : (Formalism.L2.Theta.mt S (o.emb (a, 1))).map f = 1 := by
  rw [OrthDec.mt_emb]
  have h1 : Formalism.L2.Theta.mt L (1 : GA D L) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1]
  have hs := congrArg (fun M : Mx D S.rank S.rank => M.map f) o.sum_eq_one
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f)] at hs ⊢
  rw [ha, Matrix.mul_one, Matrix.mul_one, hs]

theorem emb_mem_grpAt {D : D7} {S A L : HSp D} (o : OrthDec S A L) (P : Pl D → Prop) {a : GA D A}
    (ha : a ∈ grpAt A P) : o.emb (a, 1) ∈ grpAt S P := by
  simp only [grpAt, congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
  have ha' : (Formalism.L2.Theta.mt A a).map (Ideal.Quotient.mk (idAt D P)) = 1 := by
    have := congrArg Units.val ha
    simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using this
  have key := emb_map_eq_one o (Ideal.Quotient.mk (idAt D P)) ha'
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using key

end GlobalTheory.FinPl


open GlobalTheory.FinPl in
theorem GlobalTheory.FinPl.emb_gl_sumFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  intro D k _ _ _ _ p n _ _ σ B β β₀ hsum g
  obtain ⟨hgrp, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨hgrpA, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
  have hmem : B.o.emb (β.gl g, 1) ∈ grpAt B.V₀ (· = p.v) := emb_mem_grpAt B.o _ ((hgrpA _).2 ⟨g, rfl⟩)
  obtain ⟨h, hh⟩ := (hgrp _).1 hmem
  rw [hh]
  congr 1
  set M := (Formalism.L2.Theta.mt B.V₀ (B.o.emb (β.gl g, 1))).map p.pr with hMdef
  have hM : M = β₀.b * h.val * β₀.b' := by rw [hMdef, hh, β₀.gl_mat]

  have hY : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB B.o B.ζ) i)) =
      B.o.jB.map p.pr * replicateCol (Fin 1) fun j => p.pr (ratV B.ζ j) := by
    ext i j

    simp [Matrix.mul_apply, ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat, map_sum, map_mul]
  have hA : M * B.o.jA.map p.pr = B.o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : M * B.o.jB.map p.pr = B.o.jB.map p.pr := by
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jB, h1, Matrix.mul_one]
  have hemb : ((embX 1 g : GL (n ⊕ Fin 1) k) : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
  have key : M * β₀.b = β₀.b * (embX 1 g).val := by
    rw [hsum, hemb, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hY]
    congr 1
    · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one,
        Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hB, Matrix.mul_zero, zero_add, Matrix.mul_one]
  apply Units.ext
  calc h.val = β₀.b' * (β₀.b * h.val * β₀.b') * β₀.b := by
        simp only [Matrix.mul_assoc, β₀.b'b, Matrix.mul_one]
        rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
    _ = β₀.b' * (M * β₀.b) := by rw [← hM, Matrix.mul_assoc]
    _ = β₀.b' * (β₀.b * (embX 1 g).val) := by rw [key]
    _ = (embX 1 g).val := by rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)

theorem _root_.GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  first | exact @GlobalTheory.FinPl.emb_gl_sumFrame | exact GlobalTheory.FinPl.emb_gl_sumFrame | (intros; apply GlobalTheory.FinPl.emb_gl_sumFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

namespace GlobalTheory.FinPl

theorem sec_mul_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) (a : AE D) (u : k) : p.sec (p.pr a * u) = a * p.sec u := by
  have h1 : p.sec (p.pr a * u) = p.sec (p.pr (a * p.sec u)) := by rw [map_mul p.pr, p.pr_sec]
  have h2 : p.e * p.sec u = p.sec u := by rw [← p.sec_pr, p.pr_sec]
  rw [h1, p.sec_pr, mul_left_comm, h2]

theorem mulVec_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) {r : ℕ} (m : Matrix (Fin r) (Fin r) (AE D)) (u : Fin r → k) :
    m *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((m.map p.pr *ᵥ u) i) := by
  funext i

  simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, sec_mul_sec]

theorem single_mem_gluedS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) :
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec := by
  refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨q.1, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
  · have h0 : (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
      funext j
      simp
    rw [h0, zero_sub]
    exact neg_mem (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Pi.single_eq_same, Unif.inv, inv_mul_cancel₀ q.ne_zero]

theorem zero_col_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), GluedCore B L₀ q β β₀ P → ∀ γ : GA D B.V₀, (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i)) ∈ latV B.V₀ L₀ (· = p.v) := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hg γ hpres
  have he : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have hvec : p.sec 1 • ratV (vecB B.o B.ζ) =
      fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, he, mulVec_single_one, hg.sum]
    simp [p.sec_pr]
  have hmem : p.sec 1 • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by
    rw [hg.unit.2, hvec, ← hg.lat]
    exact single_mem_gluedS q P
  have := hpres _ hmem
  rwa [hg.unit.2, hvec] at this

theorem orbitGlued (D : D7) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ)
      (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1))
      (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
      ∀ γ ∈ grpAt B.V₀ (· = p.v),
        (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
          mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
        (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
        ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k),
          β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat := by
  intro k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ hγ hpres
  obtain ⟨hF1, -, -, hF4, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨h, rfl⟩ := (hF1 γ).1 hγ
  have key : ∀ x, mt B.V₀ (β₀.gl h)⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) ↔
      x ∈ h • gluedS q 1 P.ker P.vec := by
    intro x
    rw [← map_inv, mulVec_sec, β₀.gl_mat, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, β₀.b'b,
      Matrix.mul_one, ← mulVec_mulVec, ← hg.lat, GlobalTheory.LatPair.mem_smul_iff]
    rfl
  have hz := (key _).1 (zero_col_mem D k p n q σ B L₀ β β₀ P hg _ hpres)
  have hint : ∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] :=
    fun x hx => GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral D k p n q σ B L₀ β β₀ P hsd hg _ hγ hpres x ((key x).2 hx)
  rcases GlobalTheory.T.smul_gluedLatticeFirstPosition_cases k n q P h hz hint with ⟨Λ, hΛ, hM | hM⟩ | ⟨g, hM⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inl fun x => by rw [← hM]; exact (key x).symm⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inr fun x => by rw [← hM]; exact (key x).symm⟩
  · obtain ⟨hA1, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hF4 L₀ hsd
    have hΛG : Λ₀ = gluedS q 1 P.ker P.vec := Submodule.ext fun x => (hΛ₀ x).trans (hg.lat x).symm
    refine Or.inl ⟨β.gl g, (hA1 _).2 ⟨g, rfl⟩, β₀.gl ((embX 1 g)⁻¹ * h), ?_, ?_⟩
    · rw [hK, hΛG, mul_smul, hM, inv_smul_smul]
    · rw [GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal D k p n σ B β β₀ hg.sum g, ← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinPl
end
end
end
