module

public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.MulAction
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
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Filtration

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CompactQuotientSubmodule

section

@[expose] public section

theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FgZ1T

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations in
/-- Apply compact-quotient finite generation to the lattice cocycles, using reduction modulo `ϖ`. -/
theorem UpperTheory.Reformulated.B.Gub2.fg_Z1T
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {LL O V : Type} [inst_2 : Field LL] [inst_3 : CommRing O] [inst_4 : Algebra O LL]
    [inst_5 : AddCommGroup V] [inst_6 : Module LL V] [inst_7 : Module O V]
    [inst_8 : IsScalarTower O LL V] {ρ : Representation LL G V}
    [inst_9 : TopologicalSpace V] [inst_10 : ContinuousAdd V] [inst_11 : ContinuousConstSMul LL V]
    [inst_12 : TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V]
    (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : algebraMap O LL ϖ ≠ 0)
    (hb : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hc : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T))
    (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG := by
  have hmem : ∀ x : L.T, x ∈ (Ideal.span {ϖ ^ 1} • (⊤ : Submodule O L.T)) ↔
      ∃ y ∈ L.T, ϖ • y = (x : V) := by
    intro x
    rw [pow_one, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  have hred : ∀ c : latticeCocycles L, redT L _ c ∈ quotientCocycles L _ hI := by
    intro c
    have hcont : Continuous (c : G → V) := c.2.1.1
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, fun g h => ?_⟩
    · have h0 : Filter.Tendsto (fun y => (c : G → V) y - (c : G → V) g) (nhds g) (nhds 0) := by
        have := (hcont.sub (continuous_const (y := (c : G → V) g))).tendsto g
        rw [Pi.sub_apply, sub_self] at this
        exact this
      filter_upwards [h0 (hb.mem_of_mem (i := 1) trivial)] with y hy
      obtain ⟨v, hv, hvy⟩ := hy
      refine (Submodule.Quotient.eq _).2 ((hmem _).2 ⟨v, hv, ?_⟩)
      rw [← pow_one ϖ]
      exact hvy
    · have : evT L (g * h) c = evT L g c + actT L g (evT L h c) :=
        Subtype.ext (c.2.1.2 g h)
      change Submodule.mkQ _ (evT L (g * h) c) = _
      rw [this, map_add (f := _)]
      rfl
  refine UpperTheory.compact_quotient_submodule (LL := LL) (latticeCocycles L) ϖ
    ((redT L _).codRestrict (quotientCocycles L _ hI) hred) hc ?_ ?_
  · intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIf, t, ht, hsub⟩ := hU
    obtain ⟨n, -, hn⟩ := hb.mem_iff.1 ((Filter.biInter_mem hIf).2 fun i _ => ht i)
    refine ⟨n, fun z hz => hsub fun i hi => ?_⟩
    exact Set.mem_iInter₂.1 (hn ⟨z i, hz.2 i trivial, rfl⟩) i hi
  · intro z hz
    have hz' : ∀ g, ∃ y ∈ L.T, ϖ • y = (z : G → V) g := fun g =>
      (hmem (evT L g z)).1
        ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Subtype.val hz) g))
    refine ⟨(algebraMap O LL ϖ)⁻¹ • (z : G → V),
      ⟨(continuousCocycles ρ).smul_mem _ z.2.1, fun g _ => ?_⟩, ?_⟩
    · obtain ⟨y, hy, h⟩ := hz' g
      have : ((algebraMap O LL ϖ)⁻¹ • (z : G → V)) g = y := by
        rw [Pi.smul_apply, ← h, ← algebraMap_smul LL ϖ y, inv_smul_smul₀ hϖ]
      rw [this]
      exact hy
    · rw [← algebraMap_smul LL ϖ, smul_inv_smul₀ hϖ]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.FinT

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_smulTop (L : Lattice (O := O) ρ) (ϖ : O) (x : ↥L.T) :
    x ∈ (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, ϖ • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem fg_Z1T [TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V] (L : Lattice (O := O) ρ) {ϖ : O}
    (h0 : algebraMap O LL ϖ ≠ 0)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hK : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T)) (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG :=
  _root_.UpperTheory.Reformulated.B.Gub2.fg_Z1T L h0 hB hK hI hfin

theorem t2Space_of_lattice_nhds_basis [IsTopologicalAddGroup V] [IsNoetherianRing O] [IsLocalRing O] (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : ¬ IsUnit ϖ)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V))) :
    T2Space V := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hcon
  push_neg at hcon
  have hin : ∀ n : ℕ, ∃ t ∈ L.T, ϖ ^ n • t = x := fun n => hcon _ (hB.mem_of_mem (i := n) trivial)
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥L.T) (Ideal.span {ϖ})
    (fun h => hϖ (Ideal.span_singleton_eq_top.1 h))
  obtain ⟨t₀, ht₀, he₀⟩ := hin 0
  have hxT : x ∈ L.T := by
    rw [pow_zero, one_smul] at he₀
    exact he₀ ▸ ht₀
  have hmem : (⟨x, hxT⟩ : ↥L.T) ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • (⊤ : Submodule O ↥L.T)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨t, ht, he⟩ := hin n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨t, ht⟩, trivial, Subtype.ext he⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx (congrArg Subtype.val hmem)

def toV (L : Lattice (O := O) ρ) : LatticeCohomology L →ₗ[O] H1V ρ :=
  Submodule.liftQ _
    (((Submodule.mkQ ((B1 ρ).comap (continuousCocycles ρ).subtype)).restrictScalars O) ∘ₗ
      { toFun := fun c => ⟨(c : G → V), c.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (by
      rintro c ⟨x, _, hx⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨x, hx⟩)

theorem toV_mk (L : Lattice (O := O) ρ) (c : ↥(latticeCocycles L)) :
    toV L (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨(c : G → V), c.2.1⟩ := rfl

theorem isLocalized_toV [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) {ϖ : O} (h0 : ϖ ≠ 0)
    (hInt : ∀ c : G → V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ L.T) :
    IsLocalizedModule (nonZeroDivisors O) (toV L) := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    have hs : algebraMap O LL (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hxy' : (s : O) • x = (s : O) • y := hxy
      rw [← algebraMap_smul LL (s : O) x, ← algebraMap_smul LL (s : O) y] at hxy'
      exact smul_right_injective _ hs hxy'
    · intro y
      refine ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩
      change (s : O) • ((algebraMap O LL (s : O))⁻¹ • y) = y
      rw [← algebraMap_smul LL (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := hInt (c : G → V) c.2.1
    have hz : ϖ ^ n • (c : G → V) ∈ latticeCocycles L :=
      ⟨(continuousCocycles ρ).restrictScalars O |>.smul_mem _ c.2, fun g _ => hn g⟩
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, ⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩⟩, ?_⟩
    rfl
  · intro x₁ x₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [toV_mk, toV_mk, Submodule.Quotient.eq] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨n, hn⟩ := hInt (fun _ => v) continuous_const
    refine ⟨⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨ϖ ^ n • v, hn 1, ?_⟩
    funext g
    have hvg : ρ g v - v = (a : G → V) g - (b : G → V) g := congrFun hv g
    change ρ g (ϖ ^ n • v) - ϖ ^ n • v = ϖ ^ n • (a : G → V) g - ϖ ^ n • (b : G → V) g
    rw [← smul_sub, ← hvg, ← algebraMap_smul LL (ϖ ^ n) v, map_smul, ← smul_sub, algebraMap_smul]

end Gen

end GlobalTheory.CompanionTheory.LocDual.FinT
end
end
end
