module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
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
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiSmulRight
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBRenameMul
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusAOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def RestPlusAW (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : Prop :=
  Formalism.GM.M.goodCount p (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
            (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D * dXi r (G.B - jp) ≤
    Formalism.GM.M.goodCount p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D

theorem plusA_of (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) (h : RestPlusAW p (r := r) G j jp D) :
    Formalism.GM.M.bad p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D ≤ badY p (r := r) G j jp D * dXi r (G.B - jp) := by
  have h1 := finrank_Ljj_le p (r := r) G j jp
  have hY : Module.finrank ℤ_[p] (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) = dimY p (r := r) G j jp :=
    Formalism.CountingSumsFrames.finrank_lattice _ _ inf_le_left
  unfold badY
  simp only [Formalism.GM.M.bad]
  rw [hY, Nat.sub_mul]
  unfold RestPlusAW at h
  omega

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusAWI (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    RestPlusAW X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 ⌊D1r C0 CE1 CE2 X CM⌋

theorem restPlusA_of (CM : ℝ) (h : RestPlusAWI C0 CE1 CE2 X CM) : RestPlusA C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  exact plusA_of X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _ (h dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MfacMapDomainAdd

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Disj

variable {k σ τ : Type} [Field k] [DecidableEq σ] [DecidableEq τ]

theorem mapDomain_add_inj (e : τ → σ) (he : Function.Injective e) (a b : τ →₀ ℕ) (β β' : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0)
    (h : Finsupp.mapDomain e a + β = Finsupp.mapDomain e b + β') : a = b ∧ β = β' := by
  have ha : a = b := by
    ext x
    have h1 := DFunLike.congr_fun h (e x)
    simpa [Finsupp.mapDomain_apply_of_injective he, hβ, hβ'] using h1
  subst ha
  exact ⟨rfl, add_left_cancel h⟩

theorem mfac_mapDomain_add (e : τ → σ) (he : Function.Injective e) (a : τ →₀ ℕ) (β : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) : (mfac (Finsupp.mapDomain e a + β) : k) = mfac a * mfac β := by
  unfold mfac
  have hd : Disjoint (Finsupp.mapDomain e a).support β.support := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact (Finsupp.mem_support_iff.1 hx') (hβ y)
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]

theorem fockK_rename_mul (e : τ → σ) (he : Function.Injective e) (A B : MvPolynomial τ k) (β β' : σ →₀ ℕ) (c : k)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0) :
    Formalism.GM.M.fockK (rename e A * monomial β 1) (rename e B * monomial β' c) =
      if β = β' then c * mfac β * Formalism.GM.M.fockK A B else 0 := by
  classical
  set F := rename e A * monomial β (1 : k) with hF
  set G := rename e B * monomial β' c with hG
  have hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m := by
    intro m
    rw [hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]
  have hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0 := by
    intro n hn
    rw [hF, MvPolynomial.coeff_mul_monomial'] at hn
    split_ifs at hn with hle
    · rw [mul_one] at hn
      obtain ⟨u, hu, hu0⟩ := MvPolynomial.coeff_rename_ne_zero e A (n - β) hn
      refine ⟨u, ?_, hu0⟩
      rw [hu]
      exact (tsub_add_cancel_of_le hle).symm
    · exact absurd rfl hn
  have hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0 := by
    intro m
    split_ifs with hb
    · subst hb
      rw [hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]
    · by_contra hne
      rw [hG, MvPolynomial.coeff_mul_monomial'] at hne
      split_ifs at hne with hle
      · have h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        obtain ⟨u, hu, -⟩ := MvPolynomial.coeff_rename_ne_zero e B _ h1
        have h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β' := by
          rw [hu]
          exact (tsub_add_cancel_of_le hle).symm
        exact hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2
      · exact hne rfl
  have hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) =
      (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k)) :=
    fun m => mfac_mapDomain_add e he m β hβ
  unfold Formalism.GM.M.fockK
  have hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β) := by
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hcF0 n (MvPolynomial.mem_support_iff.1 hn)
    exact Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn]
    ring)]
  have hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support :=
    fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1
  rw [Finset.sum_image hinj]
  simp only [hcF, hcG, hmf]
  split_ifs with hb
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold mfac
    ring
  · simp

end Disj

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PlusAWICondition

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mono_mem_xiPolZ (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    monomial m (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  obtain ⟨h1, h2, -⟩ := xiMons_spec (r := r) G n m hm
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    have hm2 : m' = m := Finset.mem_singleton.1 (support_monomial_subset hm')
    subst hm2
    exact ⟨h1, h2⟩
  · exact ⟨monomial m 1, by simp⟩

theorem pderiv_chain_mono (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (a : Fin N) (c : Fin r) : pderiv (Sum.inl (Fin.castSucc a, c)) (monomial m (1 : ℚ_[p])) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  rw [pderiv_monomial]
  have : m (Sum.inl (Fin.castSucc a, c)) = 0 := by
    by_contra hne
    obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
    simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
    exact absurd hd.1 (Fin.castSucc_ne_last a)
  rw [this]
  simp

theorem mono_chain_zero (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (x : Fin N × Fin r) : m (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  by_contra hne
  obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
  exact absurd hd.1 (Fin.castSucc_ne_last x.1)

theorem chainEmb_inj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
  intro x y h
  simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem cf_mul (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (((n.factorial / (m.prod fun _ k => k.factorial) : ℕ) : ℚ_[p]) * (mfac m : ℚ_[p])) = (n.factorial : ℚ_[p]) := by
  obtain ⟨-, -, h3⟩ := xiMons_spec (r := r) G n m hm
  have hdvd : (m.prod fun _ k => k.factorial) ∣ n.factorial := by
    have := Nat.prod_factorial_dvd_factorial_sum m.support m
    rw [h3] at this
    exact this
  have e : (mfac m : ℚ_[p]) = ((m.prod fun _ k => k.factorial : ℕ) : ℚ_[p]) := by
    unfold mfac Finsupp.prod
    push_cast
    rfl
  rw [e, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

theorem plusAW_of_blockOK (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : RestPlusAW p (r := r) G j jp D := by
  classical
  unfold RestPlusAW
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D
  have hcard : (xiMons (r := r) G (G.B - jp)).card = dXi r (G.B - jp) := card_xiMons_eq (r := r) G (G.B - jp)
  let e := Fintype.equivFin (Fin (Formalism.GM.M.goodCount p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D) × (xiMons (r := r) G (G.B - jp)))
  let cfn : (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) → ℕ := fun m => (G.B - jp).factorial / (m.prod fun _ k => k.factorial)
  have hXm : ∀ k, rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
      Ljj p (r := r) G j jp := fun k =>
    Submodule.subset_span ⟨x (e.symm k).1, hx _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
  have hYm : ∀ k, ((cfn (e.symm k).2.1 : ℕ) : ℚ_[p]) •
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p])) ∈
      Ljj p (r := r) G j jp := by
    intro k
    have h1 : rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
        Ljj p (r := r) G j jp :=
      Submodule.subset_span ⟨y (e.symm k).1, hy _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
    have h2 := Submodule.smul_mem (Ljj p (r := r) G j jp) ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]) h1
    rw [algebra_compatible_smul ℚ_[p] ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]), map_natCast] at h2
    exact h2
  have hpair : ∀ k k', bePhi p (r := r) G j jp
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]))
      (((cfn (e.symm k').2.1 : ℕ) : ℚ_[p]) •
        (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k').1) * monomial (e.symm k').2.1 (1 : ℚ_[p]))) =
      if k = k' then (p : ℚ_[p]) ^ D else 0 := by
    intro k k'
    obtain ⟨⟨i, m, hm⟩, hk⟩ : ∃ q, e.symm k = q := ⟨_, rfl⟩
    obtain ⟨⟨i', m', hm'⟩, hk'⟩ : ∃ q, e.symm k' = q := ⟨_, rfl⟩
    have hkk : k = k' ↔ (i = i' ∧ m = m') := by
      constructor
      · rintro rfl
        rw [hk] at hk'
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk'
        exact hk'
      · rintro ⟨rfl, rfl⟩
        exact e.symm.injective (hk.trans hk'.symm)
    rw [hk, hk']
    dsimp only
    rw [bePhi_smul_right]
    unfold bePhi
    rw [phisB_rename_mul p (r := r) G hB j jp _ _ (fun a c => pderiv_chain_mono p (r := r) G (G.B - jp) m hm a c),
      fockK_rename_mul _ (chainEmb_inj (r := r) G) _ _ m m' 1 (mono_chain_zero (r := r) G (G.B - jp) m hm)
        (mono_chain_zero (r := r) G (G.B - jp) m' hm')]
    have hxy' : Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
        ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) = if i = i' then (p : ℚ_[p]) ^ D else 0 := hxy i i'
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl]
      have hcf := cf_mul p (r := r) G (G.B - jp) m hm
      have hdeg : (degFact G j jp : ℚ_[p]) =
          (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]) := by
        unfold degFact; push_cast; rfl
      have hF : Formalism.GM.M.fockK (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') := rfl
      have hP : (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun a _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hn0 : ((G.B - jp).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      rw [hdeg, hF]
      have key : ((cfn m : ℕ) : ℚ_[p]) *
          (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) := by
        rw [show ((cfn m : ℕ) : ℚ_[p]) *
            (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
            (((cfn m : ℕ) : ℚ_[p]) * mfac m) * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p])) by ring]
        rw [hcf]
        field_simp
      rw [key, hxy']
      by_cases hii : i = i'
      · rw [if_pos hii, if_pos (hkk.2 ⟨hii, rfl⟩)]
      · rw [if_neg hii, if_neg (fun h => hii (hkk.1 h).1)]
    · rw [if_neg hmm, if_neg (fun h => hmm (hkk.1 h).2)]
      simp
  have hmem := le_csSup (gcL_bdd p (r := r) G j jp D) ⟨fun k => _, fun k => _, hXm, hYm, hpair⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hcard] at hmem
  exact hmem

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem plusAWICondition (CM : ℝ) : RestPlusAWI C0 CE1 CE2 X CM := by
  intro dl _ aTop _ x _
  exact plusAW_of_blockOK X.p (gB C0 CE1 CE2 X aTop 0 x.1) (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _

theorem plusACondition (CM : ℝ) : RestPlusA C0 CE1 CE2 X CM :=
  restPlusA_of C0 CE1 CE2 X CM (plusAWICondition C0 CE1 CE2 X CM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
