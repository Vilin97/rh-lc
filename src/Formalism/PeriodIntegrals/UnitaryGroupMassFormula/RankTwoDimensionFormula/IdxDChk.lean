module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxADAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
public import Formalism.SatakeDualWeyl.StatementC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDMatP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAdP

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain

namespace PI.UnitaryDimensionFormula

section
variable {F : Type} [Field F] [NumberField F]

theorem adAd_natCast_apply (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (g : FiniteAdeleRing (𝓞 F) F) v = (g : v.adicCompletion F) :=
  map_natCast (Formalism.UG.evalV F v) g

theorem adAd_val_g (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g : v.adicCompletion F) = v.intValuation (g : 𝓞 F) := by
  have e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F) := by
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F) := (map_natCast _ g).symm
  rw [e2, HeightOneSpectrum.valuation_of_algebraMap]

theorem adAd_val_lt (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  rw [adAd_val_g]; exact (v.intValuation_lt_one_iff_mem _).2 h

theorem adAd_val_one (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) = 1 := by
  rw [adAd_val_g]
  exact (v.intValuation_eq_one_iff_mem_primeCompl _).2 h

def adOfInt (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

theorem adOfInt_int (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : adOfInt f hf ∈ Formalism.UG.intAd F := hf

end

theorem idxDAd : IdxDAd := by
  intro F _ _ g
  let P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (g : 𝓞 F) ∈ v.asIdeal
  have h01 : ∀ v : HeightOneSpectrum (𝓞 F),
      (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  let e := adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01
  refine ⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0
    split_ifs <;> simp
  · have ht : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]
    refine ⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (1 : v.adicCompletion F) - (if P v then 1 else 0) =
      (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)
    rw [adAd_natCast_apply]
    split_ifs with hv
    · simp
    · have hne : (g : v.adicCompletion F) ≠ 0 := by
        intro h0
        have := adAd_val_one g v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [sub_zero, mul_inv_cancel₀ hne]
  · intro c hc
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), P v →
        Valued.v (1 + (g : v.adicCompletion F) * c v) = 1 := by
      intro v hv
      have hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1 := by
        rw [map_mul]
        have hcv : Valued.v (c v) ≤ 1 := hc v
        calc Valued.v (g : v.adicCompletion F) * Valued.v (c v) ≤ Valued.v (g : v.adicCompletion F) * 1 :=
              mul_le_mul' le_rfl hcv
          _ < 1 := by rw [mul_one]; exact adAd_val_lt g v hv
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
    have hy : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]
      · exact zero_mem _
    refine ⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) *
      (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0
    rw [adAd_natCast_apply]
    split_ifs with hv
    · have hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0 := by
        intro h0
        have := hu v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [one_mul, mul_inv_cancel₀ hne]
    · simp

end PI.UnitaryDimensionFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAsm

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [hrow, Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  have key : ∀ (a c : Fin n → A) (t : A), (t • Matrix.vecMulVec a c) *ᵥ y = (t * (c ⬝ᵥ y)) • a := by
    intro a c t
    funext q
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsum : ∀ (s : Finset (Fin k)) (f : Fin k → Matrix (Fin n) (Fin n) A),
      (∑ i ∈ s, f i) *ᵥ y = ∑ i ∈ s, f i *ᵥ y := by
    intro s f
    classical
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]
  unfold sMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, key, key, hrow_dot, hrow_dot]

end Alg

variable {D : D7} {X : HidaSetting D}

theorem sMat_Lf (hI : IdxDInt) (b bs : Fin D.R.k → VA X.B.I) (hb : ∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf)
    (C D' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ (D' - 1) i j ∈ IntAf X.B.I.F X.B.I.E)
    (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    sMat (sigA X.B.I) (JA X.B.I) b bs C D' *ᵥ y ∈ X.B.I.Lf := by
  rw [sMat_mulVec]
  refine X.B.I.Lf.add_mem hy (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  have h1 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (bs j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).2 _ hy
  have h2 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (b j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).1 _ hy
  refine X.B.I.Lf.add_mem ?_ ?_
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).1 h1⟩ (hb i).1
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).2 h2⟩ (hb i).2

theorem one_sub_int (i j : Fin D.R.k) (C : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : C i j ∈ IntAf X.B.I.F X.B.I.E) : (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem hC (one_mem _)
  · simpa using hC

theorem fmat_inv_fix (x : X.B.I.Gf) (w : VA X.B.I) (h : X.B.I.fmat x *ᵥ w = w) : X.B.I.fmat x⁻¹ *ᵥ w = w := by
  have h1 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    first
    | simp [Formalism.MainNotions.S.AutInst.fmat]
    | (simp only [Formalism.MainNotions.S.AutInst.fmat]
       rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one])
  calc X.B.I.fmat x⁻¹ *ᵥ w = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ w) := by rw [h]
    _ = (X.B.I.fmat x⁻¹ * X.B.I.fmat x) *ᵥ w := by rw [Matrix.mulVec_mulVec]
    _ = w := by rw [h1, Matrix.one_mulVec]

theorem fixV_of (u : D.what₂.Word) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y ∈ fixV X u := by
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).1]
    exact Or.inl (Or.inl ⟨a, rfl⟩)
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).2]
    exact Or.inl (Or.inr ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr rfl

theorem idxSurj_of (hAlg : IdxDAlg) (hAd : IdxDAd) (hI : IdxDInt) (hSig : IdxDSig) (hFr : IdxDFrame)
    (hMat : IdxDMat) (hLev : IdxDLevi) : IdxSurj := by
  intro D X Y u _ A
  obtain ⟨e, he⟩ := hAd X.B.I.F X.B.g
  obtain ⟨b, bs, hfr, hL, hperp, hcong⟩ := hFr D X u e he
  obtain ⟨C, C', hCC, hint, hres⟩ := hMat D X Y.TR e he A
  obtain ⟨hinv, hherm⟩ := hSig X.B.I
  obtain ⟨hfix, hcomp, hone, hunit⟩ :=
    hAlg _ (sigA X.B.I) X.B.I.n D.R.k (JA X.B.I) (epsX X e) b bs hinv hherm hfr
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  set σ := sigA X.B.I with hσ
  set s := sMat σ (JA X.B.I) b bs C (C'.map σ)ᵀ with hs
  set sI := sMat σ (JA X.B.I) b bs C' (C.map σ)ᵀ with hsI
  have hmapT : ∀ M N : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), M * N = 1 →
      (N.map σ)ᵀ * (M.map σ)ᵀ = 1 := by
    intro M N hMN
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have h1 : s * sI = 1 := by
    rw [hs, hsI, hcomp, hCC', hmapT C C' hCC']
    exact hone 1 1 (by simp) (by simp)
  have h2 : sI * s = 1 := by
    rw [hs, hsI, hcomp, hCC, hmapT C' C hCC]
    exact hone 1 1 (by simp) (by simp)
  let u0 : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := ⟨s, sI, h1, h2⟩
  have hmem : u0 ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := hunit C C' hCC
  let s' : X.B.I.Gf := ⟨u0, hmem⟩
  have hfs : X.B.I.fmat s' = s := rfl
  have hintS : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C'.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C (hint i j).1, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).2)⟩
  have hintI : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C' (hint i j).2, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).1)⟩
  have hK : s' ∈ X.B.I.Kset := by
    show ∀ x, x ∈ X.B.I.Lf ↔ s *ᵥ x ∈ X.B.I.Lf
    intro x
    constructor
    · exact sMat_Lf hI b bs hL C _ hintS x
    · intro hx
      have := sMat_Lf hI b bs hL C' _ hintI _ hx
      rwa [← hsI, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this
  have hfixs : ∀ w ∈ fixV X u, s *ᵥ w = w := by
    intro w hw
    exact hfix C _ w fun j => hperp j w hw
  let sF : Hfin X u := ⟨X.xu u * s' * (X.xu u)⁻¹, by
    intro y hy
    have e1 : X.B.I.fmat (X.xu u * s' * (X.xu u)⁻¹) =
        X.B.I.fmat (X.xu u) * X.B.I.fmat s' * X.B.I.fmat (X.xu u)⁻¹ := rfl
    have e2 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
      have : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = X.B.I.fmat (X.xu u * (X.xu u)⁻¹) := rfl
      rw [this, mul_inv_cancel]; rfl
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfs, hfixs _ (fixV_of u y hy),
      Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]⟩
  have hcj : cj X u sF = s' := by
    show (X.xu u)⁻¹ * (X.xu u * s' * (X.xu u)⁻¹) * X.xu u = s'
    group
  refine ⟨sF, ?_, ?_⟩
  · rw [hcj]; exact hK
  · rw [hcj]
    funext v
    have hM : leviM Y.TR s' v = ((A v : GL (Fin D.R.k) (Y.TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (Y.TR.Fq v)) := by
      ext i j
      rw [← hres v i j]
      exact hLev D X Y.TR e he b bs hfr hL hcong C C' hCC hint v i j
    unfold levi
    split_ifs with hdet
    · ext i j
      show leviM Y.TR s' v i j = _
      rw [hM]
    · exact absurd (by rw [hM]; exact (A v).isUnit.map Matrix.detMonoidHom) hdet

end PI.UnitaryDimensionFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk

section

@[expose] public section

namespace PI.UnitaryDimensionFormula

theorem idxSurj_of_frame (hFr : IdxDFrame) : IdxSurj :=
  idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi

end PI.UnitaryDimensionFormula
end
end
