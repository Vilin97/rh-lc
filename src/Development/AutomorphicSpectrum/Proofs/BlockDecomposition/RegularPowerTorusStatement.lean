module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqZeroOfInfiniteRange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowersDiagonalAtTBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaGLMemIwGL
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactClosureZpowersMap

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.TwSide

section Generic

variable {G : Type} [Group G]

end Generic

section Diag

variable {L : Type} [Field L]

theorem thetaGL_diagT (c : L →+* L) {n : ℕ} (u : Fin n → Lˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT L (Fin n) u) =
      GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.map (c : L →* L) (u i.rev)⁻¹ := by
  apply Units.ext
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero,
      mul_zero]

theorem exists_diagT {n : ℕ} (g : GL (Fin n) L) (h : ∀ i j : Fin n, i ≠ j → g.val i j = 0) :
    ∃ s : Fin n → Lˣ, g = GlobalTheory.SmGL.diagT L (Fin n) s := by
  have hne : ∀ i, g.val i i ≠ 0 := by
    intro i h0
    have h1 : (g.val * (g⁻¹).val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [h i k hk, zero_mul]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

end Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_diagT_of_mem_TO {n : ℕ} {w : Pl E} {τ : GLw n w} (hτ : τ ∈ TO n w) :
    ∃ v : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (v i : w.adicCompletion E) = 1) ∧
      τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
  obtain ⟨v, hv⟩ := exists_diagT τ hτ.1
  refine ⟨v, fun i => ?_, hv⟩
  have h := hτ.2 i
  rw [hv, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at h
  exact h

theorem nrmL_diagT {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (u : Fin n → (w.adicCompletion E)ˣ) :
    nrmL n w (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n)
        fun i => u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ := by
  rw [nrmL, if_neg hw, thetaGL_diagT, ← map_mul]
  rfl

theorem ordL_norm_entry (hU : Unr E) {n : ℕ} {w : Pl E} (u : Fin n → (w.adicCompletion E)ˣ) (y : Fin n → ℤ)
    (hu : ∀ i, ordL (u i : w.adicCompletion E) = y i) (i : Fin n) :
    ordL ((u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = nv y i := by
  obtain ⟨-, -, hcv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hinv : ordL (((u i.rev)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    have h1 := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i.rev).ne_zero ((u i.rev)⁻¹).ne_zero
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one, hu] at h1
    omega
  have hmap : ordL ((Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    rw [← hinv]
    exact GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (hcv _)
  rw [Units.val_mul, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i).ne_zero (Units.ne_zero _), hu, hmap]
  simp only [nv]
  omega

end GlobalTheory.CompanionTheory.TwSide
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationQuotientSeparatedDvd

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MT PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RegPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open GlobalTheory.CompanionTheory.MatchPow in
theorem hasVals_nrm (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a : ℕ}
    {y : Fin a → ℤ} (hy : StrictAnti y) {δ : GLw a w} (hδ : dcos a w (tdiag ϖ y) δ ≠ 0) :
    HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨m, -, τ, hτ, e⟩ := GlobalTheory.CompanionTheory.ThetaContraction.contr_tw hU w hw ϖ hϖ a y hy δ hδ
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.CompanionTheory.TwSide.exists_diagT_of_mem_TO hτ
  have hdu : m⁻¹ * δ * thL a w m = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) fun i => ϖ ^ y i * v i := by
    rw [e, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (((ϖ ^ y i * v i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y i := by
    intro i
    simp only [Units.val_mul]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ.1,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  rw [← GlobalTheory.CompanionTheory.MatchLinear.charpoly_nrmL_twConj hU a w δ m, hdu, GlobalTheory.CompanionTheory.TwSide.nrmL_diagT hw, GlobalTheory.SmGL.val_diagT,
    Matrix.charpoly_diagonal]
  exact ⟨fun i => _, rfl, fun i => ⟨Units.ne_zero _, GlobalTheory.CompanionTheory.TwSide.ordL_norm_entry hU _ y hord i⟩⟩


open GlobalTheory.CompanionTheory.MatchPow in
theorem mpow_entT {w : Pl E} {n : ℕ} (a : ℕ) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, fun s => ?_⟩
    funext y
    have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
      (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
    rw [pow_zero, one_mul]
    exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e, mconv_entT GlobalTheory.CompanionTheory.DcosProduct.dcosMul n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem regPowT : RegPowT := by
  intro E _ _ _ hU n d _ hm a ha m w hT y hy
  obtain ⟨hw, -, hϖ, hc⟩ := hm.T w hT
  rw [GlobalTheory.CompanionTheory.MatchLMB2.trace_test_function_eq d ha hT m] at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨J', _, c', x', hx', e⟩ := mpow_entT a hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w)
    (fun j => hc j.1 j.2) m
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.qT_eq d s, GlobalTheory.CompanionTheory.MatchLMPlaces.mpow_scale, e s] at hs
  have h1 : entT n w (d.ϖ w) a c' x' s y ≠ 0 := fun h => hs (by simp [h])
  by_cases hA : MT.admitted n a s
  swap
  · exact absurd (dif_neg hA) h1
  unfold entT at h1
  rw [dite_eq_left hA] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hd2 : dcos (n - a) w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.2)) y.2 ≠ 0 := right_ne_zero_of_mul hj
  have hd1 : dcos a w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.1)) y.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hj)
  obtain ⟨u₁, hQ₁, hu₁⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.1) hd1
  obtain ⟨u₂, hQ₂, hu₂⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.2) hd2
  rw [hQ₁, hQ₂]
  exact GlobalTheory.CompanionTheory.SymmetricIndexRegularity.localization_quotient_separated_dvd (fun z => ordL z) (hx' j).1 _ _ hA.2.2.2.1 hA.2.2.2.2 (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ s)
    (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ sᶜ) (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_disj n _ _ s (by have := hA.2.2.1; omega)) u₁ u₂
    (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.RegPow

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorusStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.regular_power_torus : PositivityTheory.Rg.BcB.F.MLM.RegPowT := by
  first | exact @GlobalTheory.CompanionTheory.RegPow.regPowT | exact GlobalTheory.CompanionTheory.RegPow.regPowT | (intros; apply GlobalTheory.CompanionTheory.RegPow.regPowT <;> assumption)
end
end
