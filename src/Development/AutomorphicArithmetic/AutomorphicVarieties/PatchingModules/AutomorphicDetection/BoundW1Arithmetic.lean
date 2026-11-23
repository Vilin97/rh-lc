module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GwBare
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocBare
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.W1BoundArithmeticRankTwo

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocCongr

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PresCounts

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presCounts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → a.Counts := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  obtain ⟨hLF, hLTD, hLEC, hGF, _, hGW, _, _⟩ := hC
  have key : ∀ (w : ArData.W Lc q) (n : ℕ),
      LocCount (↥(Dec (P.A w))) ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n →
        LocCount (a.D w) (G.ε.comp (a.ι w)) n := by
    intro w n hn
    refine locCongr l (a.D w) (↥(Dec (P.A w))) (P.α w) (G.ε.comp (a.ι w))
      ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n ?_ hn
    intro g
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [P.ι_eq w g, P.e_ε]
  have notl : ∀ (w : ArData.W Lc q), (∀ v, w ≠ Sum.inl v) →
      LocCount (a.D w) (G.ε.comp (a.ι w)) 0 := by
    intro w hw
    apply key
    refine (locBare hLF hLTD hLEC l F Ω (P.A w) (↑(P.pl w)) (P.isOver w)).2 ?_
    rw [P.pl_l]
    rintro ⟨v, hv⟩
    exact hw v hv
  have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
  refine ⟨?_, ?_, ?_, ?_, hU⟩
  · rw [hcw]
    exact gwBare hGW hLTD hGF hLF l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A a.D a.ι P.α d P.ip P.c
      hl P.above P.e_ε P.isOver P.ι_eq P.cc
  · intro v
    have h1 := (locBare hLF hLTD hLEC l F Ω (P.A (Sum.inl v)) (↑(P.pl (Sum.inl v))) (P.isOver _)).1
      ((P.pl_l _).2 ⟨v, rfl⟩)
    rw [← P.dv_eq v] at h1
    exact key (Sum.inl v) _ h1
  · intro u
    exact notl (Sum.inr (Sum.inl u)) (fun v h => by cases h)
  · intro j
    exact notl (Sum.inr (Sum.inr j)) (fun v h => by cases h)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArSys

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.arSys :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T), V0.S' = s.S → Nonempty (ArSys T (Module.finrank ℚ (Lp L)) V0.frame.D0) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P hS
  choose a p h1 h2 h3 using arPres l L Ω s V0 O n r T P hS
  exact ⟨{
    a := a
    counts := fun N =>
      presCounts hP l _ _ _ _ (a N) (Lp L) Ω (p N) s.odd (unrLoc l L Ω s V0 O n r)
    dv := fun v : Vl l L => locDeg v.1
    dv_eq := fun N => funext (h1 N)
    d0 := h2
    ph := fun N j => (h3 N j).1
    ta := fun N j => (h3 N j).2 }⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.B1abs

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.b1abs :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : ArSys T d D0) (d' : L.Vl → ℕ), l ≠ 2 → ∑ v, d' v = d → (∀ v, Nonempty (LocAb l (L.Gv v) (L.Iv v) (d' v))) → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → x.N4 D0 → T.Eig x al → Detects k (Set.range T.sg) → T.B1 k (n * d + n * T.q) := UpperTheory.V.Pa.W1_bound_arithmetic_rank_two
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.BoundW1Arithmetic

section

@[expose] public section

namespace UpperTheory.V.Pa

theorem b1Ar : FirstOrderDualArithmeticBound := by
  intro hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD
  obtain ⟨d', hsum, hab⟩ := hloc
  obtain ⟨A⟩ := arSys hcoh l L Ω s V0 O n r T x0 hS
  refine b1abs l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab
    (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD
  rw [← hsum]
  first
    | exact (finsum_eq_sum_of_fintype _).symm
    | (convert (finsum_eq_sum_of_fintype d').symm)

end UpperTheory.V.Pa
end
end
