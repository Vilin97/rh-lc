module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DigAbs
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickLem
public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickLem
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds

-- Source module: Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FactorLeProductSeven

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem lowest_weight_le_of_isotypic (D : Formalism.BasicNotions.D7) {R : Type} [Field R] [CharZero R] {ι : Type} [Fintype ι] (LL : Letters ι)
    {n : ℕ} [NeZero n] (S : Set ι) (lam : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R)
    (hF : F ∈ isoSub (glOps R n LL S) lam) : lam1S LL S F ≤ ((lam 0 : ℤ) : WithBot ℤ) := by
  obtain ⟨ee, hee, _⟩ := Formalism.MainNotions.G.Joints.polIsoDecompB_of D (weight_condition_from_integral_form D) R ι LL n S
  refine (((valuation_field D).2 R ι LL n S ee hee).2 F (lam 0)).2 fun mu hmu => ?_
  by_cases h : lam = mu
  · rw [h]
  · exact absurd ((hee mu).2 lam h F hF) hmu

section DD

variable {σ Kf : Type} [Field Kf]

theorem coeff_mon_divDer (m a : σ →₀ ℕ) (F : MvPolynomial σ Kf) :
    (monomial m (1 : Kf) * divDer m F).coeff a = (∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : Kf)) * F.coeff a := by
  rw [coeff_monomial_mul']
  split_ifs with hma
  · rw [one_mul]
    unfold divDer
    rw [coeff_sum]
    have hsingle : ∀ b ∈ F.support, b ≠ a →
        AddMonoidAlgebra.coeff (if m ≤ b then monomial (b - m) (F.coeff b * ((m.prod fun k j => (b k).choose j : ℕ) : Kf))
          else 0) (a - m) = 0 := by
      intro b _ hb
      split_ifs with hmb
      · rw [coeff_monomial, if_neg]
        intro h
        apply hb
        have h1 : b - m + m = a - m + m := by rw [h]
        rwa [tsub_add_cancel_of_le hmb, tsub_add_cancel_of_le hma] at h1
      · simp
    by_cases ha : a ∈ F.support
    · rw [Finset.sum_eq_single a hsingle (fun h => absurd ha h), if_pos hma, coeff_monomial, if_pos rfl]
      unfold Finsupp.prod
      push_cast
      ring
    · rw [Finset.sum_eq_zero (fun b hb => hsingle b hb (fun h => ha (h ▸ hb))), notMem_support_iff.1 ha, mul_zero]
  · have : ∃ v, a v < m v := by
      by_contra hcon
      push Not at hcon
      exact hma hcon
    obtain ⟨v, hv⟩ := this
    have hvs : v ∈ m.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [Finset.prod_eq_zero hvs (by rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero]), zero_mul]

end DD

section BC

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem diagK_binomCombF (lam : (σ →₀ ℕ) →₀ O) (F : MvPolynomial σ (KK O)) :
    diagK (fun a => binomCombF (K := KK O) lam a) F =
      ∑ m ∈ lam.support, (algebraMap O (KK O) (lam m)) • (monomial m (1 : KK O) * divDer m F) := by
  ext a
  rw [coeff_diagK, coeff_sum]
  unfold binomCombF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, coeff_mon_divDer, smul_eq_mul]
  ring

theorem geQ_binomCombF (S : UniformizedDVR p O) (lam : (σ →₀ ℕ) →₀ O) (a : σ →₀ ℕ) :
    geQ (vK p (binomCombF (K := KK O) lam a)) 0 := by
  unfold binomCombF
  refine geQ_sum _ _ fun m _ => ?_
  have h : algebraMap O (KK O) (lam m) * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : KK O) =
      algebraMap O (KK O) (lam m * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : O)) := by
    rw [map_mul, map_prod]
    simp
  rw [h]
  exact geQ_alg S _

end BC

theorem padicVal_expFact_le' (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (α : ι × Fin k →₀ ℕ) (hα : ∀ s, multideg α s = d s) :
    padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : ι, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

section St

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coefGe_of_inBB [hp : Fact p.Prime] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) {ι : Type} [Fintype ι]
    {k : ℕ} (d : ι → ℕ) (Z : MvPolynomial (ι × Fin k) (KK O)) (hZ : Z ∈ Pol (KK O) k d) (hBB : InBB (O := O) p Z) :
    CoefGe p (((algebraMap O (KK O) w) ^ (padicValNat p (∏ s, (d s).factorial))) • Z) 0 := by
  intro bn
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hbn : bn ∈ Z.support
  · have hdeg : ∀ s, multideg bn s = d s := ((mem_restrictSupport_iff (KK O)).1 hZ) hbn
    have h1 := padicVal_expFact_le' p d bn hdeg
    have h2 : (0 : WithTop ℚ) ≤ vK p (Z.coeff bn) + (((padicValNat p (expFact bn) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
      le_trans hBB (vBB_le_coeff Z bn)
    intro q hq
    rw [valuation_mul_alt, vK_w_pow hp.out S w hw2] at hq
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 hq
    rw [← hb, ← WithTop.coe_add] at h2
    have h3 : (0 : ℚ) ≤ b + (padicValNat p (expFact bn) : ℚ) / 2 := by exact_mod_cast h2
    have h4 : a = ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) / 2 := by exact_mod_cast ha
    have h5 : ((padicValNat p (expFact bn) : ℕ) : ℚ) ≤ ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) := by
      exact_mod_cast h1
    have h6 : (0 : ℚ) ≤ q := by rw [← hab, h4]; linarith
    exact_mod_cast h6
  · rw [notMem_support_iff.1 hbn, mul_zero]
    exact geQ_zero 0

end St

end Formalism.MainNotions.Proposition5Numerics
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.VBBMonomialOne

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem vBB_monomial_one {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}
    (nu : σ →₀ ℕ) :
    vBB (O := O) p (monomial nu (1 : KK O)) = (((padicValNat p (expFact nu) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  unfold vBB
  rw [support_monomial, if_neg one_ne_zero, Finset.inf_singleton, coeff_monomial, if_pos rfl, valuation_one_eq_zero_alt, zero_add]

theorem monomial_mem_pol {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (d : ι → ℕ) (nu : ι × Fin n →₀ ℕ)
    (hnu : ∀ x, multideg nu x = d x) : (monomial nu (1 : Kf)) ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff]
  intro mo hmo
  have : mo = nu := by
    rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hmo
    by_contra h
    exact hmo (if_neg fun h' => h h'.symm)
  rw [this]
  exact hnu

theorem noAt (D : Formalism.BasicNotions.D7) (p : ℕ) [hpF : Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O))
    (hDA : DigAbs p O) (Fr : Frames n' r) {J : ℕ} [NeZero J] (cP : ℕ) (Dt : SignedChainData p O r J) :
    NoAt (K := K) p O Fr cP Dt := by
  intro dNo ka rho e nu hrho hJ hnu
  have hp := hpF.out
  have : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  obtain ⟨_, _, hJ3, hJ4⟩ := hJ
  obtain ⟨W, hW⟩ : ∃ W, W = algebraMap O (KK O) w := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = padicValNat p (∏ x, (dNo x).factorial) := ⟨_, rfl⟩
  obtain ⟨vn, hvn⟩ : ∃ vn, vn = padicValNat p (expFact nu) := ⟨_, rfl⟩
  obtain ⟨Dno, hDno⟩ : ∃ Dno, Dno = DnoOf (K := K) p Dt.nL dNo := ⟨_, rfl⟩
  have hvW : ∀ n : ℕ, vK p (W ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := fun n => by
    rw [hW]; exact vK_w_pow hp S w hw2 n
  have hWn0 : ∀ n : ℕ, W ^ n ≠ 0 := by
    intro n h
    have := hvW n
    rw [h, valuation_zero_alt] at this
    exact WithTop.top_ne_coe this
  have hpW : (p : KK O) = W ^ 2 := by rw [hW, ← map_pow, hw2, map_natCast]
  have hmon : (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := monomial_mem_pol dNo nu hnu

  have hUpol : (W ^ vn)⁻¹ • (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := Submodule.smul_mem _ _ hmon
  have hUBB : InBB (O := O) p ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    unfold InBB
    rw [vBB_smul _ (inv_ne_zero (hWn0 vn)), vK_inv _ _ (hvW vn), vBB_monomial_one, ← hvn, ← WithTop.coe_add]
    simp
  obtain ⟨hZ1, hZ2⟩ := hJ3 _ hUpol
  have hZBB := hZ2 hUBB
  rw [← hDno] at hZBB
  have hYint := coefGe_of_inBB S w hw2 dNo _ (Submodule.smul_mem _ ((p : KK O) ^ Dno) hZ1) hZBB
  rw [← hW, ← hn2] at hYint
  obtain ⟨cY, hcY⟩ : ∃ cY, cY = W ^ n2 * (p : KK O) ^ Dno * (W ^ vn)⁻¹ := ⟨_, rfl⟩
  have hY : cY • e (monomial nu 1) = W ^ n2 • (p : KK O) ^ Dno • e ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    rw [map_smul, smul_smul, smul_smul, hcY]
  rw [← hY] at hYint
  obtain ⟨Yy, hYy⟩ : ∃ Yy, Yy = cY • e (monomial nu 1) := ⟨_, rfl⟩
  rw [← hYy] at hYint
  have hYpol : Yy ∈ Pol (KK O) K dNo := by
    rw [hYy]
    exact Submodule.smul_mem _ _ (hJ3 _ hmon).1
  obtain ⟨lam, hlam1, hlam2⟩ := (hDA (TL J Dt.nL r × Fin K) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.natAdd r v.2)) (fun v => hrho _ _)).2 true cP
  have hlam3 : ∀ bn : TL J Dt.nL r × Fin K →₀ ℕ,
      geQ (vK p (binomCombF (K := KK O) lam bn - ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹)) (cP : ℝ) := by
    intro bn
    have h := geQ_neg _ (hlam2 bn)
    rw [neg_sub, if_pos rfl] at h
    exact h
  refine ⟨diagK (fun bn => binomCombF (K := KK O) lam bn) Yy, cY, ⟨?_, diagK_mem_pol _ _ hYpol, ?_⟩, ?_, ?_⟩
  · intro bn
    rw [coeff_diagK]
    have := geQ_mul _ _ (geQ_binomCombF S lam bn) (hYint bn)
    rwa [add_zero] at this
  · intro j u hu
    rw [diagK_binomCombF]
    have h1 := (degree_truncation D (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL j u) cP lam.support hlam1
      (fun m => algebraMap O (KK O) (lam m)) Yy).2
    have h2 : lam1S Dt.trueLet (NSet Dt.nL j u) Yy ≤ ((ka j u 0 : ℤ) : WithBot ℤ) := by
      rw [hYy]
      exact lowest_weight_le_of_isotypic D Dt.trueLet (NSet Dt.nL j u) (ka j u) _
        (Submodule.smul_mem _ _ (hJ4 (monomial nu 1) ⟨j, ⟨u, by omega⟩⟩))
    refine le_trans h1 (le_trans (add_le_add_left h2 _) ?_)
    rw [← WithBot.coe_add]
    push_cast
    exact le_rfl
  · refine ⟨(n2 : ℚ) / 2 + (Dno : ℚ) - (vn : ℚ) / 2, ?_, ?_⟩
    · rw [hcY, valuation_mul_alt, valuation_mul_alt, hvW, vK_inv _ _ (hvW vn), hpW, ← pow_mul, hvW, ← WithTop.coe_add,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring
    · rw [← hn2, ← hvn, ← hDno]
      push_cast
      exact le_rfl
  · rw [← hYy]
    intro bn
    rw [MvPolynomial.coeff_sub, coeff_diagK, coeff_diagK, ← sub_mul]
    have := geQ_mul _ _ (hlam3 bn) (hYint bn)
    rwa [add_zero] at this

end Formalism.MainNotions.Proposition5Numerics
end
end
end
