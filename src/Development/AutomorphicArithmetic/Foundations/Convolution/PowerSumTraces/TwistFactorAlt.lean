module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.TwistedTraces.IntegralOperatorFixedInvariantOfLeftInvariantKer
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsCompactOpenFamilyInfFixedNeBot
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicIntersectionProductEq
public import Development.AutomorphicArithmetic.TwistedTraces.LeClosureSpanAllOfCommutingUnitaryReps
import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
import Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsAlgHomEndIntertwiningMemAdjoin
public import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
public import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.TwistedTraces.SummandLeClosureSpanLocalTypeImages
import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalFixedVectorsIsotypicOfIrreducib

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (K : Subgroup G), IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K) → fixedVectors τ K ≠ ⊥ → ∀ t : Module.End ℂ (fixedVectors τ K), ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ ∀ x : fixedVectors τ K, A x = t x := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π K hKc hKo hfd hne t
  haveI := hfd
  haveI : Nontrivial (fixedVectors τ K) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let b : G → Module.End ℂ (fixedVectors τ K) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype
  have he : ∀ y : fixedVectors τ K, e y = y := fun y =>
    Subtype.ext (fixedProj_apply_of_mem hτ hKc hKo y.2)
  have hq : ∀ f, Eqv τ π ⊤ f → ∀ x, prj (fixU π K) (f x) = f (e x) := fun f hf x =>
    UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf x
  have hcomm : ∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H),
      (∀ g h v, π g (π' h v) = π' h (π g v)) →
        ∀ h v, prj (fixU π K) (π' h v) = π' h (prj (fixU π K) v) := by
    intro G' _ _ π' hc
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1
  have htop : Algebra.adjoin ℂ (Set.range b) = ⊤ := by
    obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ K) (fixedVectors τ K) {LinearMap.id}
      (Set.range fun g => (b g, b g)) (by simp) (by
        rintro _ ⟨g, rfl⟩ _ rfl
        rfl) (by
        intro x hx
        let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
          refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩⟩
        have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
          rcases eq_bot_or_eq_top W with h | h
          · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
            have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
            rw [h', map_one] at this
            exact (hx (Subtype.ext this)).elim
          · exact congrArg Subrepresentation.toSubmodule h
        rw [eq_top_iff]
        rintro y -
        rw [← he y]
        refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
        rintro _ ⟨g, rfl⟩
        exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
    rw [eq_top_iff]
    intro s _
    have hcs : c s = s := by simpa using h1 s LinearMap.id rfl
    rw [← hcs]
    refine Algebra.adjoin_mono ?_ (h2 s)
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  have ht : t ∈ Algebra.adjoin ℂ (Set.range b) := by rw [htop]; trivial
  induction ht using Algebra.adjoin_induction with
  | mem s hs =>
    obtain ⟨g, rfl⟩ := hs
    refine ⟨prj (fixU π K) ∘L π g ∘L prj (fixU π K),
      (fixedVectors τ K).subtype ∘ₗ e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype ∘ₗ e,
      ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact p3 D hD hinv _ (hinv g _ (p3 D hD hinv _ hv))
    · intro G' _ _ π' hc h v
      show prj (fixU π K) (π g (prj (fixU π K) (π' h v))) = π' h (prj (fixU π K) (π g (prj (fixU π K) v)))
      rw [hcomm G' π' hc h v, hc, hcomm G' π' hc]
    · intro f hf x
      show prj (fixU π K) (π g (prj (fixU π K) (f x))) = f (e (τ g (e x)))
      rw [hq f hf x, ← hf.map, hq f hf]
    · intro x
      show ((e (τ g ((e (x : S) : fixedVectors τ K) : S)) : fixedVectors τ K) : S) = _
      rw [he x]
      rfl
  | algebraMap z =>
    refine ⟨z • prj (fixU π K), z • ((fixedVectors τ K).subtype ∘ₗ e),
      ⟨fun v => (fixU π K).smul_mem z (p1 v), fun x => (fixedVectors τ K).smul_mem z (e x).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.smul_mem z (p3 D hD hinv _ hv)
    · intro G' _ _ π' hc h v
      show z • prj (fixU π K) (π' h v) = π' h (z • prj (fixU π K) v)
      rw [hcomm G' π' hc h v, map_smul]
    · intro f hf x
      show z • prj (fixU π K) (f x) = f (z • ((e x : fixedVectors τ K) : S))
      rw [hq f hf x, map_smul]
    · intro x
      show z • ((e (x : S) : fixedVectors τ K) : S) = _
      rw [he x]
      simp [Module.algebraMap_end_apply]
  | add s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ + T₂, A₁ + A₂, ⟨fun v => (fixU π K).add_mem (a1 v) (b1 v),
      fun x => (fixedVectors τ K).add_mem (a2 x) (b2 x), ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.add_mem (a3 D hD hinv v hv) (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (π' h v) + T₂ (π' h v) = π' h (T₁ v + T₂ v)
      rw [a4 G' π' hc, b4 G' π' hc, map_add (f := _)]
    · intro f hf x
      show T₁ (f x) + T₂ (f x) = f (A₁ x + A₂ x)
      rw [a5 f hf, b5 f hf, map_add (f := _)]
    · intro x
      show A₁ x + A₂ x = _
      rw [a6 x, b6 x]
      rfl
  | mul s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ ∘L T₂, A₁ ∘ₗ A₂, ⟨fun v => a1 _, fun x => a2 _, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact a3 D hD hinv _ (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (T₂ (π' h v)) = π' h (T₁ (T₂ v))
      rw [b4 G' π' hc, a4 G' π' hc]
    · intro f hf x
      show T₁ (T₂ (f x)) = f (A₁ (A₂ x))
      rw [b5 f hf, a5 f hf]
    · intro x
      show A₁ (A₂ x) = _
      rw [b6 x, a6 (u x)]
      rfl
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.TwistedIntertwinerFixedVectorsOfIrreducible

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (s : G ≃ₜ* G) (I : S ≃ₗ[ℂ] S), (∀ g x, I (τ g x) = τ (s g) (I x)) → (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K)) → ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → fixedVectors τ K ≠ ⊥ → ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (t : ℂ), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ HasFinTrace (A ∘ₗ (I : S →ₗ[ℂ] S)) t ∧ t ≠ 0 := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π s I hI hfd K hKc hKo hne
  let sK : Subgroup G := K.map s.toMulEquiv.toMonoidHom
  have hsKc : IsCompact (sK : Set G) := by
    have : (sK : Set G) = s '' (K : Set G) := rfl
    rw [this]
    exact hKc.image s.continuous
  have hsKo : IsOpen (sK : Set G) := by
    have : (sK : Set G) = s.toHomeomorph '' (K : Set G) := rfl
    rw [this]
    exact s.toHomeomorph.isOpenMap _ hKo
  let K₁ : Subgroup G := K ⊓ sK
  have hK₁c : IsCompact (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKc.inter hsKc
  have hK₁o : IsOpen (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hsKo
  have hPle : ∀ x ∈ fixedVectors τ K, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.1
  have hsle : ∀ x ∈ fixedVectors τ sK, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.2
  have hne₁ : fixedVectors τ K₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := hPle x hx
    rwa [h] at this
  have hIm : ∀ x ∈ fixedVectors τ K, I x ∈ fixedVectors τ sK := by
    rintro x hx _ ⟨k, hk, rfl⟩
    show τ (s k) (I x) = I x
    rw [← hI, hx k hk]
  have hIs : ∀ y ∈ fixedVectors τ sK, I.symm y ∈ fixedVectors τ K := by
    intro y hy k hk
    apply I.injective
    rw [hI, I.apply_symm_apply]
    exact hy _ ⟨k, hk, rfl⟩
  let ε : S →ₗ[ℂ] fixedVectors τ sK := fixedProj τ hτ hsKc hsKo
  let h : Module.End ℂ (fixedVectors τ K₁) :=
    LinearMap.codRestrict (fixedVectors τ K₁)
      ((I.symm : S →ₗ[ℂ] S) ∘ₗ (fixedVectors τ sK).subtype ∘ₗ ε ∘ₗ (fixedVectors τ K₁).subtype)
      (fun x => hPle _ (hIs _ (ε x).2))
  obtain ⟨T₀, A₀, ⟨c1, c2, c3, c4, c5⟩, c6⟩ :=
    UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible G H S τ hτ hirr π K₁ hK₁c hK₁o (hfd K₁ hK₁c hK₁o) hne₁ h
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let A : S →ₗ[ℂ] S := (fixedVectors τ K).subtype ∘ₗ e ∘ₗ A₀
  let B : S →ₗ[ℂ] S := A ∘ₗ (I : S →ₗ[ℂ] S)
  have hB : ∀ x ∈ fixedVectors τ K, B x = x := by
    intro x hx
    have hIx := hIm x hx
    have h1 : A₀ (I x) = x := by
      have h2 := c6 ⟨I x, hsle _ hIx⟩
      have h3 : ((ε (I x) : fixedVectors τ sK) : S) = I x := fixedProj_apply_of_mem hτ hsKc hsKo hIx
      have h4 : ((h ⟨I x, hsle _ hIx⟩ : fixedVectors τ K₁) : S) = I.symm (ε (I x) : fixedVectors τ sK) := rfl
      rw [h4, h3, I.symm_apply_apply] at h2
      exact h2
    show ((e (A₀ (I x)) : fixedVectors τ K) : S) = x
    rw [h1]
    exact fixedProj_apply_of_mem hτ hKc hKo hx
  have hR : LinearMap.range B = fixedVectors τ K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (e _).2
    · intro x hx
      exact ⟨x, hB x hx⟩
  haveI hfdR : FiniteDimensional ℂ (LinearMap.range B) := by
    rw [hR]
    exact hfd K hKc hKo
  haveI : Nontrivial (LinearMap.range B) := by
    rw [hR]
    exact Submodule.nontrivial_iff_ne_bot.2 hne
  have hrest : (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (hB y (hR ▸ y.2))
  refine ⟨prj (fixU π K) ∘L T₀, A, (Module.finrank ℂ (LinearMap.range B) : ℂ),
    ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ⟨hfdR, ?_⟩, ?_⟩
  · intro D hD hinv v hv
    exact p3 D hD hinv _ (c3 D hD hinv v hv)
  · intro G' _ _ π' hc g v
    show prj (fixU π K) (T₀ (π' g v)) = π' g (prj (fixU π K) (T₀ v))
    rw [c4 G' π' hc, ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1]
  · intro f hf x
    show prj (fixU π K) (T₀ (f x)) = f (e (A₀ x))
    rw [c5 f hf]
    exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf _
  · show LinearMap.trace ℂ (LinearMap.range B) (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = _
    rw [hrest, LinearMap.trace_id]
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.IsotypicMultiplicityTensorProduct

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_multiplicity_tensor_product :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
  by_cases hZ : Z = ⊥
  · refine ⟨0, fun U T A t hU _ _ _ _ _ _ => ?_⟩
    have hb : (Z ⊓ ⨅ i, fixU (π i) (U i)) = ⊥ := by rw [hZ, bot_inf_eq]
    haveI := hadm U hU
    rw [zero_mul, (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i))
      ((List.ofFn T).prod ∘L R)).1 0 ?_, map_zero]
    intro v
    have hv0 : (v : H) = 0 := by
      have h : ∀ w ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), w = 0 := by
        rw [hb]
        simp
      exact h _ v.2
    simp [hv0]
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hZ
  obtain ⟨hS, -⟩ := UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm hZ
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmF : ∀ i (L U : Subgroup (G i)), L ≤ U → ∀ v ∈ fixU (π i) U, v ∈ fixU (π i) L :=
    fun i L U h v hv u hu => hv u (h hu)
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hSK : ∀ i (K : Subgroup (G i)), IsCompact (K : Set (G i)) → IsOpen (K : Set (G i)) →
      FiniteDimensional ℂ (fixedVectors (τ i) K) := by
    intro i K hc ho
    have h := hS (Function.update U₀ i K) (fun j => by
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        exact ⟨hc, ho⟩
      · rw [Function.update_of_ne e]
        exact hU₀ j) i
    rwa [Function.update_self] at h
  haveI hfd0 : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) := hadm U₀ hU₀
  obtain ⟨h1, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV U₀ hU₀ hfd0 h0
  have hex := fun i => UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (s i) (I i) (hI i)
    (hSK i) (U₀ i) (hU₀ i).1 (hU₀ i).2 (h1 i).2
  choose T₀ A₀ t₀ hP ht₀ ht₀0 using hex
  have a1 : ∀ i v, T₀ i v ∈ fixU (π i) (U₀ i) := fun i => (hP i).1
  have a2 : ∀ i, ∀ x, A₀ i x ∈ fixedVectors (τ i) (U₀ i) := fun i => (hP i).2.1
  have a3 : ∀ i, ∀ v ∈ Z, T₀ i v ∈ Z := fun i => (hP i).2.2.1 Z hZc (hZi i)
  have a4 : ∀ i j, i ≠ j → ∀ h v, T₀ i (π j h v) = π j h (T₀ i v) := fun i j hij =>
    (hP i).2.2.2.1 (G j) (π j) (hcm i j hij)
  have a5 : ∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T₀ i (f x) = f (A₀ i x) := fun i => (hP i).2.2.2.2
  have hprod : (∏ i, t₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht₀0 i
  obtain ⟨κ₀, hκ₀⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI U₀ hU₀ h0
  refine ⟨κ₀, fun U T A t hU b1 b3 b4 b5 b2 bt => ?_⟩
  have hL : ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hle0 := hmono (fun i => U i ⊓ U₀ i) U₀ fun i => inf_le_right
  have hleU := hmono (fun i => U i ⊓ U₀ i) U fun i => inf_le_left
  have hneL : (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun e => h0 (le_bot_iff.1 (e ▸ hle0))
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) := hadm _ hL
  haveI hfdU : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) := hadm U hU
  obtain ⟨κ, hκ⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
    (fun i => U i ⊓ U₀ i) hL hneL
  have e1 := hκ T₀ A₀ t₀ (fun i v => hmF i _ _ inf_le_right _ (a1 i v)) a3 a4 a5
    (fun i x => hmS i _ _ inf_le_right (a2 i x)) ht₀
  have e2 := hκ₀ T₀ A₀ t₀ a1 a3 a4 a5 a2 ht₀
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T₀).prod ∘L R)).2 hle0 fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U₀ T₀ a1 a3 a4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  have hκκ : κ = κ₀ := mul_right_cancel₀ hprod (by rw [← e1, ← e2, e3])
  have e4 := hκ T A t (fun i v => hmF i _ _ inf_le_left _ (b1 i v)) b3 b4 b5
    (fun i x => hmS i _ _ inf_le_left (b2 i x)) bt
  have e5 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T).prod ∘L R)).2 hleU fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U T b1 b3 b4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  rw [← e5, e4, hκκ]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactorAlt

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.ConvolutionTheory.C.twistFactor :
    UpperTheory.ConvolutionTheory.C.TwistFactor := by
  intro K _ _ n μ _ V Z r w _ _ τ s I R hV hw hτ hZV hZ0 hZi hadm hRZ hRs hI
  classical
  have hfix : ∀ U : ∀ i, Subgroup (Gw n (w i)),
      (Z ⊓ ⨅ i, fixU (locU μ (w i)) (U i)) = Z ⊓ ⨅ i, fixL μ (w i) (U i) := fun U => by
    simp only [fixU_locU]
  have hinv : ∀ i, (locU μ (w i)).IsInvariant Z := fun i g v hv => hZi i g v hv
  have hcomm : ∀ i j, i ≠ j → ∀ (g : Gw n (w i)) (h : Gw n (w j)) v,
      locU μ (w i) g (locU μ (w j) h v) = locU μ (w j) h (locU μ (w i) g v) := by
    intro i j hij g h v
    have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.2.1 (w j) (fun e => hij (hw e.symm)) g h
    let ρ := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom
      (MultiplicityOne.finProj K n) (MultiplicityOne.continuous_finProj (K := K) (n := n))
    change ρ (AdelicGLn.localEmbedding (w i) g) (ρ (AdelicGLn.localEmbedding (w j) h) v) =
      ρ (AdelicGLn.localEmbedding (w j) h) (ρ (AdelicGLn.localEmbedding (w i) g) v)
    simp only [← UnitaryRep.map_mul_apply, hc]
  obtain ⟨c, hc⟩ := UpperTheory.isotypic_multiplicity_tensor_product r (fun i => Gw n (w i)) (LL μ) (fun i => (τ i).V) (fun i => locU μ (w i))
    (fun i => (τ i).ρ) V Z (fun i => (τ i).smooth) (fun i => (τ i).irred) hcomm hZ0 hZV hinv
    (fun i => UpperTheory.summand_le_closure_span_local_type_images K n μ V (w i) (τ i) hV (hτ i)) (fun U hU => by rw [hfix]; exact hadm U hU)
    s I R hRZ (fun i g v hv => hRs i g v hv) hI
  refine ⟨c, ?_⟩
  intro U m φ T t hU hm _ hφ hT ht
  choose A hA hAt using ht
  have hf := fun i => by
    haveI := hm i
    exact UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel (Gw n (w i)) (LL μ) (τ i).V (locU μ (w i)) (τ i).ρ (m i) (φ i) (T i) (A i) (U i)
      (fun u v => hT i u v) (hA i) (hφ i)
  have hfin := hc U T A t hU (fun i v => (hf i).1 v) (fun i v hv => (hf i).2.2.1 Z hZ0 (hinv i) v hv)
    (fun i j hij h v => (hf i).2.2.2.1 (locU μ (w j) h)
      (fun g v => hcomm i j hij g h v)
      (fun g v => by rw [UnitaryRep.adjoint_map]; exact hcomm i j hij g h⁻¹ v) v)
    (fun i f hf' x => (hf i).2.2.2.2 f hf' x) (fun i x => (hf i).2.1 x) hAt
  rw [hfix] at hfin
  exact hfin
end
end
