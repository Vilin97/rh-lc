module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
public import Development.AutomorphicArithmetic.BlochKatoExtensions.BkExtHolds
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeEveryTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto
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
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfUTieRec
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfUnramifiedLifting
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.SharpRestriction.LevelLetterCocycles.Realised2Pf
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfComplMax

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open IsLocalRing

namespace ComplMaxPf

variable {R : Type} [CommRing R]

theorem isAdicComplete_of_pow {I J : Ideal R} (e : ℕ) (he : 1 ≤ e) (h1 : ∀ k, J ^ (e * k) ≤ I ^ k)
    (h2 : ∀ k, I ^ k ≤ J ^ k) (hI : IsAdicComplete I R) : IsAdicComplete J R := by
  have m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤ := fun k => Submodule.smul_mono_left (h1 k)
  have m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤ := fun k => Submodule.smul_mono_left (h2 k)
  refine { haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)),
           prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.prec' (fun k => f (e * k)) fun {m n} hmn =>
    SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := Nat.le_mul_of_pos_left n he
  exact (hf hn).trans (SModEq.mono (m2 n) (hL n))

end ComplMaxPf

theorem complMax_holds : ComplMax := by
  intro O _ _ _ p hpm hp0 hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      rw [pow_zero, mul_one] at hu
      rw [hu] at hpm
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit
    · exact h
  have hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k) := fun k => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]
  refine ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc
  rw [hIk k]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)

end Formalism.MainNotions.N.Ln03.Pf
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtBc

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {LL' O' : Type} [Field LL'] [Algebra Qp LL'] [TopologicalSpace LL'] [CommRing O'] [Algebra O' LL']
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem comp_inj {E : Type} [Field E] [Algebra Qp E] (ι : LL →ₐ[Qp] LL') :
    Function.Injective (fun τ : E →ₐ[Qp] LL => ι.comp τ) := by
  intro τ τ' h
  apply AlgHom.ext
  intro x
  exact ι.toRingHom.injective (congrArg (fun f : E →ₐ[Qp] LL' => f x) h)

theorem comp_bij {E : Type} [Field E] [Algebra Qp E] [FiniteDimensional Qp E] (ι : LL →ₐ[Qp] LL')
    (hcard : Nat.card (E →ₐ[Qp] LL) = finrank Qp E) :
    Function.Bijective (fun τ : E →ₐ[Qp] LL => ι.comp τ) :=
  (comp_inj ι).bijective_of_nat_card_le (hcard ▸ card_algHom_le_finrank Qp E LL')

variable [Fintype (K →ₐ[Qp] LL)] [Fintype (K →ₐ[Qp] LL')]

theorem thmELiftAt_bc (ι : LL →ₐ[Qp] LL') (v' : AddValuation LL' (WithTop ℚ))
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hfin : FiniteDimensional Qp LL') (hv' : v' (PD.p : LL') = 1)
    (hO' : ∃ hO : IsDomain O', @IsDiscreteValuationRing O' _ hO ∧ IsFractionRing O' LL')
    (hBC : BCAt PD (LL := LL) (O := O) (O' := O') ι)
    (H : ThmELiftAt PD (O := O') n (fun i => ι.comp (emb i)) v') :
    ThmELiftAt PD (O := O) n emb v := by
  intro hL h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨T₁', T₂', F', hc₁', hc₂', hon', hj, -, hlift, -⟩ := hBC T₁ T₂ F hc₁ hc₂ hon
  apply hlift
  have := PD.finK
  have := PD.finK₀
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hL
  have hbK := comp_bij (E := K) ι (by rw [Nat.card_eq_fintype_card]; exact hG.1.2)
  have hbK₀ := comp_bij (E := K₀) ι (by
    rw [← Nat.card_congr (Equiv.ofBijective emb l4), Nat.card_zmod, l3])
  have hL' : Letters PD LL' v' (fun i => ι.comp (emb i)) :=
    ⟨l1, hfin, l3, hbK₀.comp l4, fun i => by
      change (ι.comp (emb (i + 1))).comp PD.σ = ι.comp (emb i)
      rw [AlgHom.comp_assoc, l5], hv'⟩
  have hG' : GoodCoeffs (K := K) (Qp := Qp) (LL := LL') (O := O') (V := T₁'.V) := by
    refine ⟨⟨hfin, ?_⟩, hc₁'.2.1, hO'⟩
    rw [← hG.1.2]
    exact (Fintype.card_of_bijective hbK).symm
  have tr₁ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₁ emb i X →
      JumpsAtE PD T₁' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).1.1 ha)
  have tr₂ : ∀ (i : ZMod n) (X : Set ℤ), JumpsAtE PD T₂ emb i X →
      JumpsAtE PD T₂' (fun i => ι.comp (emb i)) i X := by
    intro i X hX τ' hτ' a ha
    obtain ⟨τ, rfl⟩ := hbK.2 τ'
    exact hX τ (comp_inj ι (by simpa [AlgHom.comp_assoc] using hτ')) a ((hj τ a).2.1 ha)
  refine H hL' h5 T₁' T₂' F' hG' hc₁' hc₂' hon' j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂
    (fun i => tr₁ i _ (hK i)) ?_ hg hS hC hT (fun i => tr₁ i _ (hb1 i)) (fun i => tr₂ i _ (hb2 i)) hW
  intro τ' a ha
  obtain ⟨τ, rfl⟩ := hbK.2 τ'
  exact hJ τ a ((hj τ a).1.1 ha)

end Formalism.MainNotions.WachCoordinates.Br
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LocalCorollaryOfDeRham

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module

variable {l : ℕ} [Fact l.Prime]

theorem fd_mu (m : ℕ) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}) := by
  classical
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have hfin : Set.Finite {x : Om l | x ^ (l ^ m) = 1} := by
    have : {x : Om l | x ^ (l ^ m) = 1} ⊆
        ((Polynomial.nthRoots (l ^ m) (1 : Om l)).toFinset : Set (Om l)) := by
      intro x hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hl).2 hx
    exact (Finset.finite_toSet _).subset this
  have := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

def richLL (K LL : FinExt l) (m : ℕ) : FinExt l :=
  ⟨(bigLL K LL).1 ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}, by
    have := (bigLL K LL).2
    have := fd_mu (l := l) m
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_richLL (K LL : FinExt l) (m : ℕ) : LL.1 ≤ (richLL K LL m).1 := (le_bigLL K LL).trans le_sup_left

theorem caseA_richLL (K LL : FinExt l) (m : ℕ) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) :
    CaseA K (richLL K LL m) :=
  ⟨hK, h2, le_rfl, fun h => absurd h h2, (le_inf le_rfl hK).trans le_sup_left, fun τ x =>
    (le_sup_left : (bigLL K LL).1 ≤ (richLL K LL m).1)
      ((le_sup_right : _ ≤ (bigLL K LL).1) (τ.fieldRange_le_normalClosure ⟨x, rfl⟩))⟩

theorem exists_prim_Om (m : ℕ) : ∃ x : Om l, IsPrimitiveRoot x (l ^ m) := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ m) (Om l))
    (Polynomial.degree_cyclotomic_pos (l ^ m) (Om l) hpos).ne'
  exact ⟨x, (Polynomial.isRoot_cyclotomic_iff).mp hx⟩

theorem prim_richLL (K LL : FinExt l) (m : ℕ) :
    ∃ ζ : ↥(richLL K LL m).1, IsPrimitiveRoot ζ (l ^ m) := by
  obtain ⟨x, hx⟩ := exists_prim_Om (l := l) m
  have hmem : x ∈ (richLL K LL m).1 :=
    (le_sup_right : _ ≤ (richLL K LL m).1) (IntermediateField.subset_adjoin _ _ hx.pow_eq_one)
  exact ⟨⟨x, hmem⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hx⟩

theorem lift_of_caseA_rich (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
      (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)),
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) n emb ((Th l).v LL) := by
  intro l _ K LL n _ emb
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  intro hL h5
  have hn := hL.2.2.1
  subst hn
  have h5' : 5 ≤ l := by rwa [(Th l).PD_p K] at h5
  have hK : K.1 ≤ MaximalUnramifiedExtension l := by
    intro x hx
    obtain ⟨y, hy⟩ := hL.1.2 ⟨x, hx⟩
    have : (y : Om l) = x := congrArg Subtype.val hy
    rw [← this]
    exact y.2.2
  set m := N (finrank ℚ_[l] ↥(K0 K))
  have hA := caseA_richLL K LL m hK (by omega)
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥(richLL K LL m).1) := Fintype.ofFinite _
  have H' : ThmELiftAt ((Th l).PD K) (O := ↥(OL (richLL K LL m))) (finrank ℚ_[l] ↥(K0 K))
      (fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      ((Th l).v (richLL K LL m)) := by
    intro hL'
    obtain ⟨a, ha⟩ := exists_rot (PD := (Th l).PD K)
      (emb := fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      (Wf l K (richLL K LL m) hA).emb_bij.2
      hL'.2.2.2.2.1 (Wf l K (richLL K LL m) hA).emb_σ
    have := thmELiftAt_rot (Wf l K (richLL K LL m) hA).emb a
      (hLift l K (richLL K LL m) hA h5' (prim_richLL K LL m))
    rw [← ha] at this
    exact this hL'
  exact thmELiftAt_bc (IntermediateField.inclusion (le_richLL K LL m)) ((Th l).v (richLL K LL m))
    emb (richLL K LL m).2 (by rw [(Th l).PD_p K]; exact (Th l).v_l _)
    ⟨inferInstance, Formalism.BasicNotions.Examples₂.LB.OL_dvr _, Formalism.BasicNotions.Examples₂.LB.OL_frac _⟩
    (hBC l K LL (richLL K LL m) (le_richLL K LL m)) H' hL h5

theorem local_theorem_of_cyclotomic_lift (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) : LiftingTheoremLocalTheory Th 800 :=
  ⟨lift_of_caseA_rich Th N Wf hLift hBC, thmEBound_holds⟩

end Formalism.MainNotions.N.Ln03
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfInputs

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def levBOfSit {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))} {E : EtSit P AI K s LL h W}
    (S : CmpSit P AI K s LL h E) : LevB W where
  levB := S.tie.levB
  mem := S.tie.levB_mem
  supp := S.tie.levB_supp



theorem local_theorem_of_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F)
    (hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hPr2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F)
    (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F)
    (h3 : adm3 D HW F) (h4 : ArchimedeanSignatureMatching D HW F C) (h7 : adm7 D HW F Cm)
    (h8 : adm8 D HW F) (h9a : adm9 D HW F) (h10 : adm10 D HW F) (h14 : adm14 D)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) : Conclusion1 D 800 := by
  refine local_theorem_of_cyclotomic_lift D.loc id (fun l _ K LL h => (HW l).W K 1 LL h.2.2)
    (fun l _ K LL h _ h5 hz => ?_) (Formalism.MainNotions.UnusedSlot80.base_change_every_theory D.loc)
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  refine crystalline_lifting_second_form (brHyp2_of_rec (D.loc l) h h5 _ ((HW l).W_s K 1 LL h.2.2)
    (hP5 l K 1 LL h.2.2) (hP6 l K 1 LL h.2.2) (hP9 l K 1 LL h.2.2) (hPr2a l K 1 LL h.2.2)
    (h3.1 l K 1 LL h.2.2) (h4 l K 1 LL h.2.2)
    (h7 l K LL h h5).1 (h9a l K LL h h5) (h10 l K LL h h5) (h14 l K LL) ?_)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨e, he⟩ := hUG l K LL h h5
  refine ⟨e, he, UpperTheory.Prune.bkExt_holds D HW F h9 hFont l K LL h h5 e he, fun hR => ?_⟩
  have hV := valRing_rec (D.loc l) LL
  have hpl := (D.loc l).PD_p K
  have : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac LL
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) :=
    (mem_maximalIdeal _).2 (not_isUnit_p ((HW l).W K 1 LL h.2.2) hV)
  have hpm' : ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
    have h' := hpm
    rwa [hpl] at h'
  have hp0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have h0' := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h0'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h0'
  have : IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Ln03.Pf.complMax_holds ↥(OL LL) l hpm' hp0 (complete_OL LL)
  obtain ⟨uZ, huZ, hutie⟩ := Formalism.MainNotions.N.Ln03.Pf.uTieRec_holds D HW l K LL h h5
  have hrich : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ finrank ℚ_[l] ↥(K0 K)) := by
    obtain ⟨ζ, hζ⟩ := hz
    exact ⟨ζ, by rw [hpl]; exact hζ⟩
  have h5' : 5 ≤ ((D.loc l).PD K).p := by rw [hpl]; exact h5
  refine realised2_pf (K := ↥K.1) (W := (HW l).W K 1 LL h.2.2) (levBOfSit ((Cm l).C K 1 LL h.2.2)) hR e uZ
    (ιZrec (D.loc l) K LL)
    ?_ ?_ ?_ ?_ ?_ ?_ ((HW l).W_s K 1 LL h.2.2) (hP4 l K 1 LL h.2.2) ?_ ?_ (hP3 l K 1 LL h.2.2)
    (hP9 l K 1 LL h.2.2) (hP5 l K 1 LL h.2.2) ?_ ?_ ?_ hV (unram_of_caseA h) hpm hrich huZ hutie he ?_ h5'
  · exact ((Cm l).C K 1 LL h.2.2).tie.levN_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.cmp_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_φ
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_φ
  · exact (h7 l K LL h h5).2
  · exact h8 l K LL h h5
  · exact hLem3 l K 1 LL h.2.2
  · exact hDdR l K LL h
  · exact (h14 l K LL).1
  · exact Formalism.MainNotions.LiftingTheory.gen_one_crys _

theorem logb_nat_nonneg_sk (p h : ℕ) (hp : 11 ≤ p) : 0 ≤ Real.logb p (h : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · apply Real.logb_nonneg
    · have : (11 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · exact_mod_cast hh

theorem corollary_monotone_in_constant (D : D7) (C C' : ℝ) (h : C ≤ C') (H : Conclusion2 D C) : Conclusion2 D C' := by
  intro l _ K LL n _ emb
  have H' := H l K LL n emb
  intro hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT hb hC
  obtain ⟨mm, k, e1, e2, e3⟩ := H' hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT
    (le_trans (by gcongr) hb) hC
  refine ⟨mm, k, e1, e2, le_trans e3 ?_⟩
  have hp : (11 : ℝ) ≤ ((D.loc l).PD K).p := by exact_mod_cast h11
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h ?_) ?_) ?_) ?_
  · positivity
  · positivity
  · have := logb_nat_nonneg_sk ((D.loc l).PD K).p (hCor b w S η sz) h11
    have h3 : (0 : ℝ) ≤ (((D.loc l).PD K).p : ℝ) - 1 := by linarith
    positivity
  · positivity

theorem corollary_local_exists_constant : ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ),
    Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F → Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F → Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F →
    adm3 D HW F → ArchimedeanSignatureMatching D HW F C → adm7 D HW F Cm → adm8 D HW F → adm9 D HW F →
    adm10 D HW F → adm12 D → adm14 D →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1) →
    Formalism.MainNotions.LocalSituation.adm9 D HW F → Formalism.MainNotions.InvariantsGenerators.LitFont D HW F →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) →
    Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → Conclusion2 D C₂ := by
  obtain ⟨C', h1', h'⟩ := corollary_of_Theorem_E
  refine ⟨max C' (4 * 800), fun D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h12 h14
    hDdR h9 hFont hUG => ?_⟩
  have hp1 := local_theorem_of_inputs D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h14 hDdR h9 hFont hUG
  refine ⟨hp1, fun C₂ h2 => ?_⟩
  refine corollary_monotone_in_constant D _ C₂ h2 ?_
  refine h' D 800 (by norm_num) hp1 h12 ?_
  intro l _ K LL n _ emb T₁ T₂ F h1 h2 hF i A hA' τ hτ a ha
  exact hA' τ hτ a ((h14 l K LL).1 T₁ T₂ F h1 h2 hF τ a ha)

end Formalism.MainNotions.N.Ln03
end
end
end
