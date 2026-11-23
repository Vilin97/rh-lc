module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.DistinguishedUnitIdeals.UnivPart
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
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
import Formalism.DistinguishedUnitIdeals.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GradedClassDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasis
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.DetectPt

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

theorem detect_pt {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) {r : ℕ} (hr : r = Module.finrank LL D)
    (g : Fin r → ℤ → D) (hsupp : ∀ j, ∃ m : ℤ, ∀ k < m, g j k = 0) (hg : ∀ j k, g j k ∈ F (-k))
    (hspan : Submodule.span LL (Set.range fun j =>
      (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) = ⊤)
    (a : Fin r → PowerSeries LL) (e : ℕ)
    (h : ∀ k : ℤ, (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k - i)) ∈ F ((e : ℤ) - k)) :
    ∀ j, PowerSeries.X ^ e ∣ a j := by
  classical
  have hanti : Antitone F := hF.1
  have hli : LinearIndependent LL
      (fun j => (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) := by
    obtain ⟨_, hrk⟩ := finrank_grQ F hF
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [Fintype.card_fin, hrk, hr])
  have key : ∀ m, m < e → ∀ j, PowerSeries.coeff m (a j) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hcl : ∀ k' : ℤ, (∑ j, PowerSeries.coeff m (a j) • g j k') ∈ F (1 - k') := by
        intro k'
        have hS := h (k' + m)
        have hle : F ((e : ℤ) - (k' + m)) ≤ F (1 - k') := hanti (by omega)
        have hS' := hle hS
        have hR : ∀ j, (∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k' + m - i)) -
            PowerSeries.coeff m (a j) • g j k' ∈ F (1 - k') := by
          intro j
          obtain ⟨mj, hmj⟩ := hsupp j
          obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, m < N ∧ ∀ i : ℕ, N ≤ i → k' + m - i < mj :=
            ⟨(k' + m - mj).toNat + m + 1, by omega, fun i hi => by
              have := Int.self_le_toNat (k' + m - mj); omega⟩
          have hsub : (Function.support fun i : ℕ => PowerSeries.coeff i (a j) • g j (k' + m - i)) ⊆
              ↑(Finset.range N) := by
            intro i hi
            rw [Function.mem_support] at hi
            simp only [Finset.coe_range, Set.mem_Iio]
            by_contra hne
            apply hi
            rw [hmj _ (hN2 i (not_lt.mp hne)), smul_zero]
          rw [finsum_eq_sum_of_support_subset _ hsub,
            ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN1)]
          simp only [add_sub_cancel_right, add_sub_cancel_left]
          refine sum_mem fun i hi => ?_
          obtain ⟨hne, -⟩ := Finset.mem_erase.mp hi
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [ih i hlt (by omega) j, zero_smul]
            exact zero_mem _
          · exact Submodule.smul_mem _ _ (hanti (by omega) (hg j (k' + m - i)))
        have hsum := sub_mem hS' (sum_mem (t := Finset.univ) fun j _ => hR j)
        rw [Finset.sum_sub_distrib, sub_sub_cancel] at hsum
        exact hsum
      have hz : ∑ j, PowerSeries.coeff m (a j) •
          (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = 0 := by
        have hmk : ∑ j, PowerSeries.coeff m (a j) •
            (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) =
            (Submodule.mkQ _) (∑ j, PowerSeries.coeff m (a j) •
              (⟨g j, fun k _ => hg j k⟩ : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
        rw [hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.mem_pi]
        intro k _
        simpa using hcl k
      exact fun j => Fintype.linearIndependent_iff.mp hli _ hz j
  intro j
  exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => key m hm j

end Formalism.MainNotions.N.Ln03.K8
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.HfracOf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem hfrac_of {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL] (a : LL) :
    ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors O) a
  refine ⟨s, x, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    exact hx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem rank_eq [IsFractionRing O LL] (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {r : ℕ} (e : Fin r → C.V)
    (hind : LinearIndependent (PowerSeries O) e)
    (hspan : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N c) :
    FiniteDimensional LL (Dc W T c) ∧ r = Module.finrank LL (Dc W T c) := by
  classical
  let hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N c) :=
    (Module.Basis.span hind).map (LinearEquiv.ofEq _ _ hspan)
  have hBasis_e : ∀ k, (hBasis k : C.V) = e k := fun k => by
    simp [hBasis, Module.Basis.span_apply]
  have hcmpLI := Pf.lvBasis_cmp_ind hP3 hmod hfrac_of hBasis hBasis_e
  let w : Fin r → Dc W T c := fun k =>
    ⟨W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩, Pf.lvBasis_cmp_e_letter hBasis hBasis_e k⟩
  have hwLI : LinearIndependent LL w :=
    LinearIndependent.of_comp (DcrisL PD T.ρ (W.emb c)).subtype hcmpLI
  have hwsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    intro x _
    have hx := Pf.lvBasis_letter_le hP3 hmod hBasis hBasis_e x.2
    have hr : (Set.range fun k => W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩) =
        (DcrisL PD T.ρ (W.emb c)).subtype '' Set.range w := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  let bD := Module.Basis.mk hwLI hwsp
  have hFD : FiniteDimensional LL (Dc W T c) := Module.Finite.of_basis bD
  refine ⟨hFD, ?_⟩
  rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]

end Formalism.MainNotions.N.Ln03.K8
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.XPowDvdOfComponents

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem X_pow_dvd_of_components {ι R : Type} [CommRing R] (F : PowerSeries (ι → R)) (e : ℕ)
    (h : ∀ i, PowerSeries.X ^ e ∣ PowerSeries.map (Pi.evalRingHom (fun _ => R) i) F) :
    PowerSeries.X ^ e ∣ F := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  funext i
  have := (PowerSeries.X_pow_dvd_iff.1 (h i)) m hm
  rw [PowerSeries.coeff_map] at this
  simpa using this

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem detect [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W) (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (ϖ : O) (ell : ℕ)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (s : ℕ) (hs : s < ell) (hfilt : IsFilt (FilD W T c s)) (e : ℕ) (y : C.V) (hy : y ∈ (latOf C).N c)
    (h : ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c y, hy⟩ k, Lb.mem T c ζ ⟨C.t c y, hy⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((e : ℤ) - k)) :
    ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ e • y' := by
  classical
  obtain ⟨r, b, hind, hspan⟩ := hfree
  have hb : ∀ j, b j ∈ (latOf C).N c := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨hfd, hr⟩ := rank_eq hP3 hmod b hind hspan
  have hy' : y ∈ Submodule.span (PowerSeries O) (Set.range b) := hspan.symm ▸ hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
  have hyN : (⟨C.t c y, hy⟩ : ↥(W.N T)) =
      ∑ j, (baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← ha, coord_t_finset_sum]
    exact Finset.sum_congr rfl fun j _ => C.t_smul c (a j) (b j)

  have hdiv : ∀ (ζ : Rs LL PD.p s) (j : Fin r), PowerSeries.X ^ e ∣ W.lev c ζ ((baseIdOf hR).d (a j)) := by
    intro ζ
    have := hfd
    refine detect_pt (FilD W T c s) hfilt hr
      (fun j k => (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ k, Lb.mem T c ζ _ k⟩ : Dc W T c))
      (fun j => ?_) (fun j k => levB_mem_fil hP4 hcrys hLb s ζ _ k)
      (span_classes hP4 hcrys hLb hmod s hfilt ζ b hb hspan)
      (fun j => W.lev c ζ ((baseIdOf hR).d (a j))) e ?_
    · obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      exact ⟨m, fun k hk => Subtype.ext (hm k hk)⟩
    · intro k
      have hk := h ζ k
      change ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ ⟨C.t c y, hy⟩ k) ∈
        FilLev W T c s ((e : ℤ) - k) at hk

      rw [← hLb, hyN, map_sum, Finset.sum_apply] at hk
      show ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
        (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) ∈
        FilLev W T c s ((e : ℤ) - k)
      suffices heq : ∀ j, ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
          (∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
            (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) =
          W.levN T c ζ ((baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T))) k by

        rw [map_sum, Finset.sum_congr rfl fun j _ => heq j]
        exact hk
      intro j
      rw [W.levN_smul]
      obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      have hfin : (Function.support fun i : ℕ => PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)).Finite := by
        refine (Finset.range ((k - m).toNat + 1)).finite_toSet.subset fun i hi => ?_
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hi
        have h0 : (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c) = 0 :=
          Subtype.ext (hm _ (by omega))
        show _ • _ = 0
        rw [h0, smul_zero]
      rw [map_finsum _ hfin]
      refine finsum_congr fun i => ?_
      rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, ← hLb]

  have hcj : ∀ j, ∃ (N : ℕ) (z : PowerSeries O),
      PowerSeries.C (ϖ ^ N) * a j = (baseIdOf hR).Bs.p s ^ e * z := by
    intro j
    refine hcompl s hs e (a j) (X_pow_dvd_of_components _ e fun ζ => ?_)
    rw [map_eval_rhoL]
    exact hdiv ζ j
  choose Nj z hz using hcj
  obtain ⟨N', u, hu⟩ := hϖ
  set Nt := ∑ j, Nj j with hNt
  set K := N' * Nt with hK
  have hlK : ∀ j, PowerSeries.C (((PD.p : ℕ) : O) ^ K) * a j =
      (baseIdOf hR).Bs.p s ^ e * (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) := by
    intro j
    have hle : Nj j ≤ Nt := Finset.single_le_sum (fun j _ => Nat.zero_le (Nj j)) (Finset.mem_univ j)
    have e1 : ((PD.p : ℕ) : O) ^ K = u ^ Nt * ϖ ^ (Nt - Nj j) * ϖ ^ Nj j := by
      rw [hK, pow_mul, hu, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm]
    rw [e1, map_mul, mul_assoc, hz j]
    ring
  set w : C.V := ∑ j, (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) • b j with hw
  have hwN : w ∈ (latOf C).N c :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j)
  have hyw : PowerSeries.C (((PD.p : ℕ) : O) ^ K) • y = (baseIdOf hR).Bs.p s ^ e • w := by
    rw [← ha, Finset.smul_sum, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, hlK j]

  have hd : (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e) =
      ∏ s' ∈ Finset.range (s + 1), pS W s' ^ (if s' = s then e else 0) := by
    rw [map_pow, BaseId.d_p, Finset.prod_eq_single s (fun s' _ hs' => by rw [if_neg hs', pow_zero])
      (fun hns => absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) hns), if_pos rfl]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O) ^ K)) = ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [BaseId.d_C, map_pow, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) 1 hcrys
      ⟨0, (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e), ⟨fun s' => if s' = s then e else 0, s + 1, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c w, hNΔ _ hwN (fun δ hδ => C.t_Δ c w δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hyw, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
end
end
