module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColGen
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesStable
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
import Formalism.SharpRestriction.GrowthBounds.PolBridge
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ZeroOfMultideg
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.BitVec

-- Source module: Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.LatticeLeSpanPsiImage

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Span

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem lattice_le_span_psi_image {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N) :
    YjtZ O (r := r) LL J M ≤ Submodule.span O (psiR (KK O) LL '' sAll LL J M) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  intro F hF
  obtain ⟨hY, G, hG⟩ := hF
  let φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap
  have hG' : MvPolynomial.map (algebraMap O (KK O)) G = F := hG
  have hY' : MvPolynomial.map (algebraMap O (KK O)) G ∈ Yjt (KK O) (r := r) LL J M := by rw [hG']; exact hY
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hY'
  have hGP : G ∈ Pol O r LL.deg := (map_mem_Pol_iff _ hinj _ G).1 hY'.1
  have hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M) :=
    mem_span_iInter hli' (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hY'.2 k))
  have h1 : F ∈ Submodule.map φ (Submodule.span O (psiR O LL '' sAll LL J M)) := ⟨G, hGs, hG⟩
  rw [Submodule.map_span, ← Set.image_comp] at h1
  have h2 : (φ ∘ psiR (r := r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x
  rwa [h2] at h1

end Span

section Xi

variable {O : Type} [CommRing O] [IsDomain O]

theorem xiVar_inj (N r t : ℕ) : Function.Injective (xiVar N r t) := by
  intro c d h
  simpa [xiVar] using h

theorem xiSpan (N r t b : ℕ) :
    XiPolZ O N r t b ≤ Submodule.span O
      {g : MvPolynomial (BVar N r t) (KK O) | ∃ γ : Fin r → ℕ, ∑ c, γ c = b ∧ g = ∏ c, X (xiVar N r t c) ^ γ c} := by
  intro f hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.1 h2
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmap : ∀ p : MvPolynomial (BVar N r t) O,
      (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial (BVar N r t) O →ₐ[O] _).toLinearMap p =
        MvPolynomial.map (algebraMap O (KK O)) p := fun p => rfl
  have hsup : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b := by
    intro m hm
    have hm' : m ∈ (MvPolynomial.map (algebraMap O (KK O)) g).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact (map_ne_zero_iff _ hinj).2 (MvPolynomial.mem_support_iff.1 hm)
    rw [hmap] at h1
    exact ((MvPolynomial.mem_restrictSupport_iff (KK O)).1 h1) (Finset.mem_coe.2 hm')

  rw [hmap, MvPolynomial.as_sum g, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  obtain ⟨hv, hb⟩ := hsup m hm
  have hmon : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) =
      ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [Finsupp.prod, ← Finset.prod_image (fun c _ c' _ h => xiVar_inj N r t h)
      (f := fun v => (X v : MvPolynomial (BVar N r t) (KK O)) ^ m v)]
    apply Finset.prod_subset
    · intro v hv'
      obtain ⟨c, rfl⟩ := hv v hv'
      exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    · intro v _ hv'
      have h0 : m v = 0 := by simpa using hv'
      rw [h0, pow_zero]
  have hprod1 : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  have hterm : MvPolynomial.map (algebraMap O (KK O)) (MvPolynomial.monomial m (g.coeff m)) =
      g.coeff m • ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [← hmon, hprod1, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one, MvPolynomial.map_monomial]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun c => m (xiVar N r t c), hb, rfl⟩)

end Xi

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem genSet_le {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (B : BlockData N) (hJ : ∀ k, B.T.J k ≤ N) :
    genSet O (r := r) B ⊆ Submodule.span O (colGens O (r := r) B) := by
  intro x hx
  simp only [genSet, Set.mem_iUnion] at hx
  obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hx
  have key : ∀ y ∈ Submodule.span O (psiR (KK O) (B.lettersAt j jp) '' sAll (B.lettersAt j jp) B.T.J B.T.thr),
      ∀ g ∈ Submodule.span O {g : MvPolynomial (BVar N r B.T.t) (KK O) |
        ∃ γ : Fin r → ℕ, ∑ c, γ c = B.B - jp ∧ g = ∏ c, X (xiVar N r B.T.t c) ^ γ c},
      ((∏ i, B.Ehat O (r := r) i ^ j i) * B.Eplus O (r := r) ^ jp *
          (∏ i, X (scalZ N r B.T.t (Fin.castSucc i)) ^ B.T.z i) * X (scalZ N r B.T.t (Fin.last B.T.t)) ^ B.zPlus) * rename (chainEmb N r B.T.t) y * g ∈ Submodule.span O (colGens O (r := r) B) := by
    intro y hy g hg
    induction hy using Submodule.span_induction with
    | mem y0 hy0 =>
      induction hg using Submodule.span_induction with
      | mem g0 hg0 =>
        obtain ⟨yy, hyy, rfl⟩ := hy0
        obtain ⟨γ, hγ, rfl⟩ := hg0
        exact Submodule.subset_span ⟨j, jp, hok, yy, hyy, γ, hγ, rfl⟩
      | zero => simp
      | add g1 g2 _ _ h1 h2 =>
        rw [mul_add]
        exact Submodule.add_mem _ h1 h2
      | smul a g1 _ h1 =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a h1
    | zero => simp
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add (f := _), mul_add, add_mul]
      exact Submodule.add_mem _ h1 h2
    | smul a y1 _ h1 =>
      rw [AlgHom.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ a h1
  exact key y (lattice_le_span_psi_image (r := r) hA2 hA3 S (B.lettersAt j jp) B.T.J B.T.thr hJ hy) g
    (xiSpan (O := O) N r B.T.t (B.B - jp) hg)

theorem blockData_J_le (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (k : Fin (blockData p S aTop aPlus m b).T.q) : (blockData p S aTop aPlus m b).T.J k ≤ 2 * s + 1 := by
  show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) ≤ 2 * s + 1
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).isLt
    omega
  · exact le_rfl

end Gen

theorem asmRTAt_of_facSys {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro _ _ X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hmem : symFam (KK O) X.p C0 CE1 CE2 X β s ∈
      liftSub C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) :=
    symFam_span β (fun j => colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) _
      (fun s' hs' => (hF X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s' hs').some.liftable S.w_irr.ne_zero) s
      (fun j => genSet_le hA2 hA3 S _ (blockData_J_le _ _ _ _ _ _) (hs j))
  obtain ⟨raw, hc, τ, hτ, hw⟩ := hmem
  exact ⟨raw, τ, hc, hτ, hw⟩

theorem restAsmRT_of_facSys {D : Formalism.BasicNotions.D7} (hA : admitted D) (h : FacSysCondition) : RestAsmRT := by
  unfold admitted at hA
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, h15, -⟩ := hA
  intro Cc hCc
  obtain ⟨T0, hT0, h1⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h2⟩ := h1 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  obtain ⟨T2, hT2, h3⟩ := h2 CE1 CE2 Cm hE1 hE2 hm
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb a b c d e =>
    asmRTAt_of_facSys (D := D) h15 h6 (h3 CYb Cde Ck CD Cb a b c d e)⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestAssumptionsOfThreeInterfaces

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Mono

variable {σ : Type} {K : Type} [CommRing K]

def IsMono (P : MvPolynomial σ K) : Prop := ∃ M : σ →₀ ℕ, P = monomial M 1

theorem IsMono.one : IsMono (1 : MvPolynomial σ K) := ⟨0, rfl⟩

theorem IsMono.X (v : σ) : IsMono (MvPolynomial.X v : MvPolynomial σ K) := ⟨Finsupp.single v 1, rfl⟩

theorem IsMono.mul {P Q : MvPolynomial σ K} (hP : IsMono P) (hQ : IsMono Q) : IsMono (P * Q) := by
  obtain ⟨a, rfl⟩ := hP
  obtain ⟨b, rfl⟩ := hQ
  exact ⟨a + b, by rw [monomial_mul, one_mul]⟩

theorem IsMono.pow {P : MvPolynomial σ K} (hP : IsMono P) (n : ℕ) : IsMono (P ^ n) := by
  obtain ⟨a, rfl⟩ := hP
  exact ⟨n • a, by rw [monomial_pow, one_pow]⟩

theorem IsMono.prod {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ K) (h : ∀ i ∈ s, IsMono (P i)) :
    IsMono (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsMono.one (σ := σ) (K := K)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

end Mono

section Std

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

theorem ioDXmono (j : Fin (numSeg X.TT)) (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    IsMono (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v)) := by
  have e : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := aeval_X _ _
  rw [e]
  exact (IsMono.X _).pow _

theorem LvDat.stdPoly_mono (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : IsMono (L.stdPoly O j) := by
  unfold LvDat.stdPoly
  refine (IsMono.mul ?_ ?_).mul ?_
  · unfold digitMon
    exact IsMono.prod _ _ fun i _ => IsMono.prod _ _ fun c _ => ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
  · unfold sTopMon
    refine IsMono.prod _ _ fun i _ => ?_
    split_ifs
    · exact ((IsMono.X _).pow _).mul ((IsMono.X _).pow _)
    · exact IsMono.one
  · simp only [map_mul, map_prod, map_pow]
    exact ((IsMono.prod _ _ fun i _ => (ioDXmono O j _).pow _).mul ((ioDXmono O j _).pow _)).mul
      (IsMono.prod _ _ fun c _ => (ioDXmono O j _).pow _)

theorem LvDat.exists_std (L : LvDat C0 CE1 CE2 mu X β) :
    ∃ Std : MonH X, (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j := by
  obtain ⟨M, hM⟩ := IsMono.prod Finset.univ (fun j => L.stdPoly O j) fun j _ => L.stdPoly_mono O j
  exact ⟨M, hM.symm⟩

end Std

theorem cov_count (s : ℕ) : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) ≤ s := by
  classical
  have h1 : ∑ i : Fin (2 * s + 1), (if decide ((i : ℕ) % 2 = 0) = true then 0 else 1) =
      (Finset.univ.filter fun i : Fin (2 * s + 1) => ¬ (i : ℕ) % 2 = 0).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) % 2 = 0 <;> simp [h]
  rw [h1]
  refine (Finset.card_le_card_of_injOn (t := Finset.range s) (fun i : Fin (2 * s + 1) => (i : ℕ) / 2) ?_ ?_).trans
    (by simp)
  · intro i hi
    have h2 : ¬ (i : ℕ) % 2 = 0 := by simpa using hi
    have h3 := i.2
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro a ha b hb hab
    have h2 : ¬ (a : ℕ) % 2 = 0 := by simpa using ha
    have h3 : ¬ (b : ℕ) % 2 = 0 := by simpa using hb
    have h4 : (a : ℕ) / 2 = (b : ℕ) / 2 := hab
    apply Fin.ext
    omega

section Psi

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem psi_facts {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N)
    (x : Tx r LL) (hx : x ∈ sAll LL J M) :
    psiR (KK O) LL x ≠ 0 ∧ ∀ k, psiR (KK O) LL x ∈ YCond (KK O) (r := r) LL (J k) (M k) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  refine ⟨(psiK_li LL hli').ne_zero x, fun k => ?_⟩
  rw [← psiR_map]
  exact (hC1 k _ (psiK_mem LL hrange x).1).2 (Submodule.subset_span ⟨x, hx k, rfl⟩)

end Psi

theorem facSysAt_of {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hC : ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hP : PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hT : TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hp : X.p.Prime := Fact.out
  haveI hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  simp only [colGens, Set.mem_setOf_eq] at hs
  choose lv jp hOK y hy γ hγ hx using hs
  let L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β := ⟨lv, jp, hOK, γ, hγ⟩
  have hs' : s = fun j => L.word O j (psiR (KK O) (L.LL j) (y j)) := funext fun j => hx j
  obtain ⟨Std, hStd⟩ := L.exists_std O
  have hfacts := fun j => psi_facts hA2 hA3 S (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J
    (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr (blockData_J_le _ _ _ _ _ _) (y j) (hy j)
  have CS := fun j => (hC X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L j (y j) (hy j)).some
  obtain ⟨P⟩ := hP X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L _ CS (fun j => (hfacts j).1) Std hStd
  rw [hs']
  exact ⟨P.toFacSys D hStd (hT X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ L Std hStd) (fun j => (hfacts j).1)
    (fun j => (hfacts j).2) (fun j => (cov_count (segS X.TT j)).trans (hHI.1.2.2.2.2.1 j).2)⟩

theorem restFacSys_of {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : FacSysCondition :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h =>
    facSysAt_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 h.1.1 h.1.2 h.2) ((hC.and hP).and hT)

theorem rest_assumptions_of_three_interfaces {D : Formalism.BasicNotions.D7} (hA : admitted D) (hC : RestCols) (hP : RestPre) (hT : RestTCore) : RestAsmRT :=
  restAsmRT_of_facSys hA (restFacSys_of hA hC hP hT)

end Formalism.MainNotions.ColumnSystems.Pf
end
end
end
