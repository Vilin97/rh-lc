module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscPointwise
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AGFrameNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DePres
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FprodNeZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.EvTEqBlockPointOfMh

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem evT_eq_blockPoint_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ, g ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g ∧
      ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
  classical
  set φ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2) with hφ
  have hφi : Function.Injective φ := fun p p' h => by
    simp only [hφ, Prod.mk.injEq] at h
    exact Prod.ext (Fin.succ_injective _ h.1) h.2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range φ := by
    intro v hv
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h0 : v.1 ≠ 0 := by
      intro h0
      have h1 := hqm s hs 0
      rw [hm] at h1
      have hz := (Finset.sum_eq_zero_iff.1 h1) v.2 (Finset.mem_univ _)
      apply (Finsupp.mem_support_iff.1 hsv)
      have e : v = (0, v.2) := Prod.ext h0 rfl
      rw [e]; exact hz
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 h0
    exact ⟨(i, v.2), Prod.ext hi rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q φ hφi hvars
  set g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ := MvPolynomial.map sg q' with hgdef
  have heval : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [← hq', evT, MvPolynomial.eval₂_rename, hgdef, MvPolynomial.eval_map]
    congr 1
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq (by rw [← hq', map_zero])
  have hg0 : g ≠ 0 := by
    intro h0
    apply hq'0
    apply MvPolynomial.map_injective sg sg.injective
    rw [← hgdef, h0, map_zero]
  have hgm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g := by
    intro s hs b
    have hs' : s ∈ q'.support := MvPolynomial.support_map_subset _ _ hs
    have hsq : Finsupp.mapDomain φ s ∈ q.support := by
      rw [← hq', MvPolynomial.support_rename_of_injective hφi]
      exact Finset.mem_image_of_mem _ hs'
    show _ = m b.succ
    rw [← hqm _ hsq b.succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finsupp.mapDomain_apply_of_injective hφi s (b, j)).symm
  exact ⟨g, hg0, hgm, heval⟩

theorem logInt_evT_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) q‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  by_cases hq : q = 0
  · subst hq
    simp [evT]
  · obtain ⟨g, hg, hgm, heq⟩ := d.evT_eq_blockPoint_of_mh sg q hq m hm hqm
    simp_rw [heq]
    exact ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable d.D (d.N + 1) _ g hg hgm

theorem integrable_log_norm_sub_log_norm (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  obtain ⟨-, -, m, hm0, hma, hmb⟩ := hab
  exact (d.logInt_evT_of_mh sg a m hm0 hma).sub (d.logInt_evT_of_mh sg b m hm0 hmb)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscHadamard

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_hadamard (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (sg : K →+* ℂ) :
    d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg ≤
      d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (Nat.succ_pos _)
  have he := hd.a4.choose_spec.1
  have hF : ∀ c, MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro c
    have := ((d.int_Nsg hd h hI2be c sg).1 d.wF (hd.a4.choose c) (by simp) (he c).1 (he c).2).neg
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.neg_apply]
    rw [← finsum_neg_distrib]
    congr 1; ext P
    rw [← finsum_neg_distrib]
    rfl
  have hR : MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      (d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          -Real.log (d.nrm c d.wF (hd.a4.choose c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) :=
    (MeasureTheory.integrable_const _).add
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2)
  have hmono := MeasureTheory.integral_mono_ae (d.integrable_log_norm_sub_log_norm hd h a b hab sg) hR
    (d.disc_pointwise hd h a b hab sg)
  have hc : ∫ _z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1),
      ((d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))))
        ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) =
      (d.del : ℝ) * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) := by simp
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _)
      ((MeasureTheory.integrable_finsetSum _ fun c _ => hF c).const_mul 2),
    hc, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun c _ => hF c] at hmono
  have hN : d.Nsg d.wF hd.a4.choose sg = ∑ c, ∫ z, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (d.nrm c d.wF (hd.a4.choose c) P) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  have hm : d.mSgP sg a b = ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := rfl
  rw [hN, hm]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OmPoly

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem om_poly (hd : d.AxH 𝒜) (h : d.S1) :
    0 ≤ d.aG h d.wF hd.a4.choose ∧ (∃ a b : KTp K d.D d.N, d.IsPres hd h a b) ∧
    ∃ Om : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h ∧ Om ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
        (fun b : Fin (d.D + 1) => if b = 0 then 0 else 2 * (d.aG h d.wF hd.a4.choose).toNat) Om := by
  exact ⟨d.aG_frame_nonneg hd h, d.de_pres hd h, d.om_is_poly hd h⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscB

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_global (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
      (Module.finrank ℚ K : ℝ) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨haG0, ⟨a, b, hab⟩, Om, hOm, hOm0, hOmH⟩ := d.om_poly hd h
  obtain ⟨hs1, hs2, heq⟩ := d.disc_product hd h hI2be a b hab Om hOm
  refine ⟨hs1, hs2, ?_⟩
  rw [heq]
  have ha4 : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := by
    first
    | exact hd.a4.choose_spec
    | exact hd.a4.choose_spec.1
    | exact fun c => hd.a4.choose_spec.1 c
    | exact fun c => ⟨hd.a4.choose_spec.1 c, hd.a4.choose_spec.2 c⟩
  have hH : d.Hgt h d.wF hd.a4.choose = d.Hgt h d.wF ta' :=
    (d.h_ind hd h hI2be).1 d.wF hd.a4.choose ta' (by simp) ha4 hta'
  have haG : d.aG h d.wF hd.a4.choose = d.aG h d.wF ta' :=
    (d.arithDegree_additive hd h).1 d.wF hd.a4.choose ta' ha4 hta'
  have hcard : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    have hc : 0 < Fintype.card (K →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
      | exact Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hc
  have hmean : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) := by
    unfold meanK
    rw [div_le_iff₀ hcard]
    calc ∑ sg, (d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg)
        ≤ ∑ sg, (d.del * Real.log d.del +
            2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) :=
          Finset.sum_le_sum fun sg _ => d.disc_hadamard hd h hI2be a b hab sg
      _ = (d.del * Real.log d.del + 2 * ((∑ k, ∑ sg,
            Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) / (Fintype.card (K →+* ℂ) : ℝ))) *
            (Fintype.card (K →+* ℂ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum, Finset.sum_comm, add_mul, mul_assoc (2 : ℝ),
            div_mul_cancel₀ _ hcard.ne']
          ring
      _ = _ := by rw [Finset.sum_div]
  have hh0 : -(ReciprocityTheory.MultiplicativeHeights.h0 Om) ≤
      2 * d.D * d.aG h d.wF hd.a4.choose * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by
    have h1 := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ Om (Nat.succ_pos _) hOm0 hOmH
    have ht : ((d.aG h d.wF hd.a4.choose).toNat : ℝ) = (d.aG h d.wF hd.a4.choose : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg haG0
    simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, eq_self_iff_true, if_true, if_false,
      ite_true, ite_false, Nat.cast_zero, zero_mul, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at h1
    rw [ht] at h1
    linear_combination h1
  rw [hH, ← haG]
  linarith [hmean, hh0]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end
