module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SumMulSumProd
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
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDegF
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ProjectionMemPartialSpan
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValLamOfSubset
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecIdentity

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

theorem plane_dec (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) (δ : ZMod J × ℤ → ℕ) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin r) O),
      (∀ i j, PlOK p O Fr deg Y N₁ G' cP Dt ka δ j (A' i j)) ∧
      homComp δ (xiPl Fr O Dt.nL Go) = ∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j) := by
  obtain ⟨hV1, hV2, -⟩ := hVB
  obtain ⟨hSp1, -⟩ := hSp
  let Cv : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)} ∪
    {q | ∃ u < Dt.nL j, q = ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)}
  have hCv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤
      valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} (homComp δ (xiPl Fr O Dt.nL Go)) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact le_trans (ceil_le_of_geZ (hV1 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
    · exact le_trans (ceil_le_of_geZ (hV2 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
  obtain ⟨N, A', hA', hF⟩ := seg_dec hA hS (homComp δ (xiPl Fr O Dt.nL Go)) Cv (fun _ => ∅) hCv
    (fun j q hq => by simp at hq)
  refine ⟨N, A', fun i j => ?_, hF⟩
  obtain ⟨hsup, hv, -⟩ := hA' i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hF' := (support_homComp δ _ mo' hmo').1
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact hSp1 mo' hF' ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (support_homComp δ _ mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · intro u hu
    exact hv ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)
      (Or.inl ⟨u, hu, rfl⟩)
  · intro u hu
    exact hv ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)
      (Or.inr ⟨u, hu, rfl⟩)

theorem normal_dec (hA : ATL) (hS : ValSlice) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) :
    ∃ (N : ℕ) (B' : Fin N → ZMod J → MvPolynomial (ℤ × Fin K) O),
      (∀ i j, NoOK p O Fr cP Dt dNo ka j (B' i j)) ∧
      xiNo Fr O K Dt.nL No = ∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j) := by
  obtain ⟨-, -, hV3⟩ := hVB
  obtain ⟨-, hSp2⟩ := hSp
  let Cl : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ))} ∪
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ))}
  have hCl : ∀ j, ∀ q ∈ Cl j,
      lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} (xiNo Fr O K Dt.nL No) ≤ ((q.2 : ℤ) : WithBot ℤ) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact (hV3 j u hu).1
    · exact (hV3 j u hu).2
  obtain ⟨N, B', hB', hF⟩ := seg_dec hA hS (xiNo Fr O K Dt.nL No) (fun _ => ∅) Cl
    (fun j q hq => by simp at hq) hCl
  refine ⟨N, B', fun i j => ?_, hF⟩
  obtain ⟨hsup, -, hl⟩ := hB' i j
  refine ⟨?_, ?_, fun u hu => ⟨?_, ?_⟩⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact (hSp2 mo' hmo').1 ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (hSp2 mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · exact hl ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ)) (Or.inl ⟨u, hu, rfl⟩)
  · exact hl ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ)) (Or.inr ⟨u, hu, rfl⟩)

theorem dec_identity {N1 N2 : ℕ} (A' : Fin N1 → ZMod J → MvPolynomial (ℤ × Fin r) O)
    (B' : Fin N2 → ZMod J → MvPolynomial (ℤ × Fin K) O) :
    ∑ q : Fin (N1 * N2), ∏ t ∈ Finset.range J, phSeg O K p Fr (t : ℤ)
        (plEmb O r K (A' (finProdFinEquiv.symm q).1 (((t : ℤ)) : ZMod J)) *
          nmEmb O r K (B' (finProdFinEquiv.symm q).2 (((t : ℤ)) : ZMod J))) =
      PhiPl Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j)) *
        PhiNo Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j)) := by

  simp only [map_sum, map_prod, PhiPl_seg, PhiNo_seg]
  rw [sum_mul_sum_prod]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine (prod_range_zmod (fun t : ℤ => phSeg O K p Fr t
    (plEmb O r K (A' (finProdFinEquiv.symm q).1 (t : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (t : ZMod J))))).trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [cast_segZ, map_mul]

end At

theorem restDecG_of (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) :
    RestDecG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH δ hocc
  obtain ⟨hvb, hsp⟩ := hVB p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH
  have hxx := hXX p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka hMH.1
  have hdd := hDd p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH δ hocc
  have hJ : J = Fr.J := hMH.1.1.1
  obtain ⟨N1, A', hA1, hA2⟩ := plane_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hC hvb hsp δ
  obtain ⟨N2, B', hB1, hB2⟩ := normal_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hvb hsp
  refine ⟨N1 * N2, fun jz x => ((δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x) : ℕ) : ℝ),
    fun q jz => plEmb O r K (A' (finProdFinEquiv.symm q).1 (jz : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (jz : ZMod J)),
    fun jz x => δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x), ?_, ?_, ?_⟩
  · intro q j hj
    have h := hxx δ (((j : ℤ)) : ZMod J) _ _ (hA1 (finProdFinEquiv.symm q).1 _) (hB1 (finProdFinEquiv.symm q).2 _)
    rw [segZ_cast j (by rw [hJ]; exact hj)] at h
    exact h
  · intro j hj x hx hWL
    have hs := segZ_cast (J := J) j (by rw [hJ]; exact hj)
    have h := hdd (((j : ℤ)) : ZMod J) x (by rw [hs]; exact hx) (by rw [hs]; exact hWL)
    rw [hs] at h
    exact h
  · rw [hA2, hB2, ← hJ]
    exact dec_identity p O Fr A' B'

end Formalism.MainNotions.Proposition5Numerics
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwistSliceCoeff

section

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section Sl

variable {ι : Type*} {n : ℕ} (T : Set ι)

def offT (mo : ι × Fin n →₀ ℕ) : ι × Fin n →₀ ℕ := mo.filter fun v => v.1 ∉ T

def onT (mo : ι × Fin n →₀ ℕ) : ι × Fin n →₀ ℕ := mo.filter fun v => v.1 ∈ T

theorem onT_add_offT (mo : ι × Fin n →₀ ℕ) : onT T mo + offT T mo = mo :=
  Finsupp.filter_add_filter_not mo _

theorem offT_support (mo : ι × Fin n →₀ ℕ) : ∀ v ∈ (offT T mo).support, v.1 ∉ T := by
  intro v hv
  rw [offT, Finsupp.support_filter, Finset.mem_filter] at hv
  exact hv.2

theorem onT_support (mo : ι × Fin n →₀ ℕ) : ∀ v ∈ (onT T mo).support, v.1 ∈ T := by
  intro v hv
  rw [onT, Finsupp.support_filter, Finset.mem_filter] at hv
  exact hv.2

theorem offT_add (a b : ι × Fin n →₀ ℕ) : offT T (a + b) = offT T a + offT T b := Finsupp.filter_add

theorem offT_eq_self (M : ι × Fin n →₀ ℕ) (h : ∀ v ∈ M.support, v.1 ∉ T) : offT T M = M :=
  (Finsupp.filter_eq_self_iff _ _).2 fun v hv => h v (Finsupp.mem_support_iff.2 hv)

theorem offT_eq_zero (m : ι × Fin n →₀ ℕ) (h : ∀ i, i ∉ T → multideg m i = 0) : offT T m = 0 := by
  ext v
  rw [offT, Finsupp.filter_apply]
  by_cases hv : v.1 ∉ T
  · rw [if_pos hv]
    have h1 := h v.1 hv
    unfold multideg at h1
    have h2 : m (v.1, v.2) ≤ ∑ c : Fin n, m (v.1, c) :=
      Finset.single_le_sum (f := fun c : Fin n => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
    rw [h1] at h2
    exact Nat.le_zero.1 h2
  · rw [if_neg hv]
    rfl

theorem multideg_onT (mo : ι × Fin n →₀ ℕ) (i : ι) (hi : i ∉ T) : multideg (onT T mo) i = 0 := by
  unfold multideg
  apply Finset.sum_eq_zero
  intro c _
  rw [onT, Finsupp.filter_apply, if_neg hi]

end Sl

def sliceT {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (T : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (M : ι × Fin n →₀ ℕ) : MvPolynomial (ι × Fin n) R :=
  ∑ mo ∈ F.support.filter (fun mo => offT T mo = M), monomial (onT T mo) (F.coeff mo)

section Sl2

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (T : Set ι) (F : MvPolynomial (ι × Fin n) R)

theorem slice_sum : F = ∑ M ∈ F.support.image (offT T), sliceT T F M * monomial M 1 := by
  have h1 : ∀ M ∈ F.support.image (offT T), sliceT T F M * monomial M 1 =
      ∑ mo ∈ F.support.filter (fun mo => offT T mo = M), monomial mo (F.coeff mo) := by
    intro M _
    rw [sliceT, Finset.sum_mul]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [monomial_mul, mul_one, ← (Finset.mem_filter.1 hmo).2, onT_add_offT]
  rw [Finset.sum_congr rfl h1,
    Finset.sum_fiberwise_of_maps_to (fun mo hmo => Finset.mem_image_of_mem (offT T) hmo)]
  exact F.as_sum

theorem slice_support (M mo' : ι × Fin n →₀ ℕ) (h : mo' ∈ (sliceT T F M).support) :
    ∃ mo ∈ F.support, offT T mo = M ∧ onT T mo = mo' := by
  obtain ⟨mo, hmo, rfl⟩ := mem_support_sum_monomial _ _ _ _ h
  exact ⟨mo, (Finset.mem_filter.1 hmo).1, (Finset.mem_filter.1 hmo).2, rfl⟩

theorem slice_supported (M : ι × Fin n →₀ ℕ) : sliceT T F M ∈ supported R {v : ι × Fin n | v.1 ∈ T} := by
  refine Subalgebra.sum_mem _ fun mo hmo => ?_
  rw [mem_supported, vars_monomial (mem_support_iff.1 (Finset.mem_filter.1 hmo).1)]
  intro v hv
  exact onT_support T mo v hv

variable (LL : Letters ι) (S : Set ι) (j : Fin n)

theorem twist_slice_off (M m : ι × Fin n →₀ ℕ) (hm : m ∈ (twistSub LL S j (sliceT T F M)).support) :
    offT T m = 0 := by
  obtain ⟨u, hu, hmu⟩ := twistSub_support LL S j _ m hm
  obtain ⟨mo, _, _, rfl⟩ := slice_support T F M u hu
  exact offT_eq_zero T m fun i hi => (hmu i).trans (multideg_onT T mo i hi)

theorem twist_slice_coeff (hST : S ⊆ T) (M : ι × Fin n →₀ ℕ) (hM : M ∈ F.support.image (offT T))
    (m : ι × Fin n →₀ ℕ) (hm : m ∈ (twistSub LL S j (sliceT T F M)).support) :
    (twistSub LL S j F).coeff (m + M) = (twistSub LL S j (sliceT T F M)).coeff m := by
  have hoff : ∀ M' ∈ F.support.image (offT T), ∀ v ∈ M'.support, v.1 ∉ T := by
    intro M' hM'
    obtain ⟨mo, _, rfl⟩ := Finset.mem_image.1 hM'
    exact offT_support T mo
  have hsum : twistSub LL S j F =
      ∑ M' ∈ F.support.image (offT T), twistSub LL S j (sliceT T F M') * monomial M' 1 := by
    conv_lhs => rw [slice_sum T F]

    rw [map_sum]
    refine Finset.sum_congr rfl fun M' hM' => ?_
    rw [map_mul, twistSub_monomial_off LL S j M' fun v hv hvS => hoff M' hM' v hv (hST hvS)]
  rw [hsum, coeff_sum, Finset.sum_eq_single M]
  · rw [coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one]
  · intro M' hM' hne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · by_contra hc
      have hc' : (twistSub LL S j (sliceT T F M')).coeff (m + M - M') ≠ 0 := left_ne_zero_of_mul hc
      have h1 := twist_slice_off T F LL S j M' _ (mem_support_iff.2 hc')
      have h2 := twist_slice_off T F LL S j M m hm
      have h3 : m + M - M' + M' = m + M := tsub_add_cancel_of_le hle
      have h4 := congrArg (offT T) h3
      rw [offT_add, offT_add, h1, h2, zero_add, zero_add, offT_eq_self T M' (hoff M' hM'),
        offT_eq_self T M (hoff M hM)] at h4
      exact hne h4
    · rfl
  · intro h
    exact absurd hM h

end Sl2

theorem valSlice : ValSlice := by
  intro R _ _ ι n _ LL T F
  refine ⟨F.support.image (offT T), sliceT T F, ?_, fun M _ => slice_supported T F M, slice_sum T F, ?_, ?_⟩
  · intro M hM
    obtain ⟨mo, _, rfl⟩ := Finset.mem_image.1 hM
    exact offT_support T mo
  · intro M _ mo' hmo'
    obtain ⟨mo, hmo, rfl, rfl⟩ := slice_support T F M mo' hmo'
    rw [onT_add_offT]
    exact hmo
  · intro M hM S hST
    refine val_lam_of_subset _ _ _ _ _ _ fun j => sDegs_subset_of _ _ _ _ _ _ _ fun k hk => ?_
    intro m
    by_cases hm : m ∈ (twistSub LL S j (sliceT T F M)).support
    · rw [← twist_slice_coeff T F LL S j hST M hM m hm]
      exact hk _
    · rw [notMem_support_iff.1 hm]
      simp

end Formalism.MainNotions.Proposition5Numerics
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembershipOfThreeParts

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem decomposition_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) : RestDecG :=
  restDecG_of atl valSlice valComp hVB hXX hDd

theorem membership_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestMemb D CLa Ck Crk Cdeg :=
  membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
end
end
end
