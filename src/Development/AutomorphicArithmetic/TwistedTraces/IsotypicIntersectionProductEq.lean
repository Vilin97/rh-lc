module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsScalarOfTwistedIntertwinerCommutingAlgebra
public import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
public import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
public import Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubspaceProductClosed
import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
public import Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.WhittakerRelevance

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.IsotypicProjectionProductCommute

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_projection_product_commute :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∃ f', Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f' ∧ ∀ x, R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (f x)) = f' (I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
  let a : Fin r → (H →L[ℂ] H) := fun j => prj (fixU (π j) (L j))
  have hcomm : ∀ p q, p ≠ q → Commute (a p) (a q) := fun p q hpq => by
    refine ContinuousLinearMap.ext fun v => ?_
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G p) (G q) H (π p) (π q) (L p) (L q)).2.2.2 (hc p q hpq)).2 v
  have hact : ∀ j, j ≠ i → ∀ g v, a j (π i g v) = π i g (a j v) := fun j hj g v =>
    ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (L j) (L i)).2.2.2 (hc j i hj)).1 g v
  obtain ⟨hprod, hQc⟩ := UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r a hcomm i
  let b : Fin r → (H →L[ℂ] H) := Function.update a i 1
  let Q : H →L[ℂ] H := (List.ofFn b).prod
  have hQa : Commute (a i) Q := hQc (a i) fun j hj => hcomm i j hj.symm
  have hQπ : ∀ g v, Q (π i g v) = π i g (Q v) := fun g v => by
    have h : Commute (π i g : H →L[ℂ] H) Q := hQc _ fun j hj => by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (hact j hj g v).symm
    exact (congrArg (fun T : H →L[ℂ] H => T v) h.eq).symm
  have hb : ∀ p q, p ≠ q → Commute (b p) (b q) := fun p q hpq => by
    by_cases hp : p = i
    · subst hp
      simp only [b, Function.update_self]
      exact Commute.one_left _
    · by_cases hq : q = i
      · subst hq
        simp only [b, Function.update_self]
        exact Commute.one_right _
      · simp only [b, Function.update_of_ne hp, Function.update_of_ne hq]
        exact hcomm p q hpq
  have hQZ : ∀ v ∈ Z, Q v ∈ Z := by
    let M : Submonoid (H →L[ℂ] H) :=
      { carrier := {T | ∀ v ∈ Z, T v ∈ Z}
        mul_mem' := fun ha hb v hv => ha _ (hb v hv)
        one_mem' := fun v hv => hv }
    have hM : Q ∈ M := by
      refine Submonoid.list_prod_mem M fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      by_cases hj : j = i
      · subst hj
        simp only [b, Function.update_self]
        exact M.one_mem
      · simp only [b, Function.update_of_ne hj]
        exact fun v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).2.2.1 Z hZc (hZi j) v hv
    exact hM
  have hQfix : ∀ j, j ≠ i → ∀ v, Q v ∈ fixU (π j) (L j) := fun j hj v => by
    have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r b hb j).1
    have h2 : Q v = a j ((List.ofFn (Function.update b j 1)).prod v) := by
      have h3 : b j = a j := Function.update_of_ne hj _ _
      change (List.ofFn b).prod v = _
      rw [h, h3]
      rfl
    rw [h2]
    exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).1 _
  let f' : S i →ₗ[ℂ] H := (R : H →ₗ[ℂ] H) ∘ₗ (Q : H →ₗ[ℂ] H) ∘ₗ f ∘ₗ ((I i).symm : S i →ₗ[ℂ] S i)
  have hf' : ∀ y, f' y = R (Q (f ((I i).symm y))) := fun y => rfl
  have hfZ : ∀ x, f x ∈ Z := fun x => (Submodule.mem_inf.1 (hf.mem x)).1
  refine ⟨f', ⟨fun y => ?_, fun g y => ?_⟩, fun x => ?_⟩
  · rw [hf']
    have hw := hQZ _ (hfZ ((I i).symm y))
    refine Submodule.mem_inf.2 ⟨hRZ _ hw, ?_⟩
    simp only [Submodule.mem_iInf]
    intro j hj u hu
    have h := hRs j ((s j).symm u) _ hw
    rw [(s j).apply_symm_apply] at h
    rw [← h, hQfix j hj _ _ (hsK j u hu)]
  · have hIs : (I i).symm (τ i g y) = τ i ((s i).symm g) ((I i).symm y) := by
      apply (I i).injective
      rw [hI, (I i).apply_symm_apply, (I i).apply_symm_apply, (s i).apply_symm_apply]
    rw [hf', hf', hIs, hf.map, hQπ, hRs i _ _ (hQZ _ (hfZ _)), (s i).apply_symm_apply]
  · have hE : Eqv (τ i) (π i) ⊤ f := ⟨fun _ => Submodule.mem_top, hf.map⟩
    have h1 := UpperTheory.fixedProjection_apply_equivariant_eq (G i) H (S i) (τ i) (hsm i) (π i) (L i) (hL i).1 (hL i).2 f hE x
    have h2 : (List.ofFn a).prod (f x) = Q (a i (f x)) := by
      rw [hprod]
      exact congrArg (fun T : H →L[ℂ] H => T (f x)) hQa.eq
    rw [hf', (I i).symm_apply_apply]
    change R ((List.ofFn a).prod (f x)) = _
    rw [h2]
    change R (Q (prj (fixU (π i) (L i)) (f x))) = _
    rw [h1]
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubmoduleProductDecomposition

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_submodule_product_decomposition :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) (J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i))), (∀ i (x : fixedVectors (τ i) (K i)), ((J i x : fixedVectors (τ i) (K i)) : S i) = I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) → (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∀ (x : fixedVectors (τ i) (K i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (K i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i)) → ∃ ρ : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), (∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), ((ρ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod v)) ∧ ∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J hJ hcf hsp
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (K i)
  let Pr : H →L[ℂ] H := (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have hPr : ∀ v ∈ Z, Pr v ∈ (Z ⊓ ⨅ j, fixU (π j) (L j)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hc i j hij)).1 h v)
  have hRX : ∀ v ∈ Z, R (Pr v) ∈ X := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hPr v hv)
    refine Submodule.mem_inf.2 ⟨hRZ _ h1, (Submodule.mem_iInf _).2 fun j u hu => ?_⟩
    have h := hRs j ((s j).symm u) _ h1
    rw [(s j).apply_symm_apply] at h
    rw [← h, (Submodule.mem_iInf _).1 h2 j _ (hsK j u hu)]
  have hm : ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f →
      ∀ x ∈ fixedVectors (τ i) (K i), f x ∈ X := fun i f hf x hx => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hf.mem x)
    refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      exact fun u hu => by rw [← hf.map, mem_fixedVectors.1 hx u hu]
    · exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 j) e
  let ρ : Module.End ℂ X := ((R : H →ₗ[ℂ] H) ∘ₗ (Pr : H →ₗ[ℂ] H) ∘ₗ X.subtype).codRestrict X
    fun v => hRX _ (Submodule.mem_inf.1 v.2).1
  refine ⟨ρ, fun v => rfl, fun i a b hab => ?_⟩
  have key : ∀ y ∈ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i),
      ∃ h : y ∈ X, ρ (c i a ⟨y, h⟩) = c i b (ρ ⟨y, h⟩) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      obtain ⟨f', hf', hff⟩ := UpperTheory.isotypic_projection_product_commute r G H S π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
      have hρ : ∀ (x' : fixedVectors (τ i) (K i)) (h : f x' ∈ X), ((ρ ⟨f x', h⟩ : X) : H) = f' (J i x') := by
        intro x' h
        rw [hJ]
        exact hff x'
      have hy := hm i f hf x hx
      refine ⟨hy, Subtype.ext ?_⟩
      have e1 : c i a ⟨f x, hy⟩ = ⟨f (a ⟨x, hx⟩), hm i f hf _ (a ⟨x, hx⟩).2⟩ :=
        Subtype.ext (hcf i a f hf ⟨x, hx⟩ _ rfl)
      have e2 : ((c i b (ρ ⟨f x, hy⟩) : X) : H) = f' (b (J i ⟨x, hx⟩)) :=
        hcf i b f' hf' (J i ⟨x, hx⟩) _ (hρ ⟨x, hx⟩ hy)
      have e3 : b (J i ⟨x, hx⟩) = J i (a ⟨x, hx⟩) := LinearMap.congr_fun hab ⟨x, hx⟩
      rw [e1, e2, e3]
      exact hρ _ _
    | zero => exact ⟨X.zero_mem, by
        show ρ (c i a 0) = c i b (ρ 0)
        simp only [map_zero]⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨p, hp⟩ := h1
      obtain ⟨q, hq⟩ := h2
      refine ⟨X.add_mem p q, ?_⟩
      show ρ (c i a (⟨u, p⟩ + ⟨v, q⟩)) = c i b (ρ (⟨u, p⟩ + ⟨v, q⟩))
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | smul k u _ h1 =>
      obtain ⟨p, hp⟩ := h1
      refine ⟨X.smul_mem k p, ?_⟩
      show ρ (c i a (k • ⟨u, p⟩)) = c i b (ρ (k • ⟨u, p⟩))
      rw [map_smul, map_smul, map_smul, map_smul, hp]
  exact LinearMap.ext fun v => (key v (hsp i v.2)).2
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.TraceRestrictEqOfHasFinTrace

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.trace_restrict_eq_of_hasFinTrace :
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (Q Q' : Submodule ℂ S) [FiniteDimensional ℂ Q'] (g : S →ₗ[ℂ] S) (t : ℂ) (m : Module.End ℂ Q') (e : Q' →ₗ[ℂ] S), Q ≤ Q' → HasFinTrace g t → (∀ x, g x ∈ Q) → (∀ x : Q', ((m x : Q') : S) = g (e x)) → (∀ x : Q', (x : S) ∈ Q → e x = x) → LinearMap.trace ℂ Q' m = t := by
  intro S _ _ Q Q' _ g t m e hQ hg hgQ hm he
  obtain ⟨hfd, hr⟩ := hg
  haveI := hfd
  have hWQ : LinearMap.range g ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hgQ x
  let p : Q' →ₗ[ℂ] LinearMap.range g :=
    (g ∘ₗ e).codRestrict (LinearMap.range g) fun x => LinearMap.mem_range_self g (e x)
  let q : LinearMap.range g →ₗ[ℂ] Q' := Submodule.inclusion (hWQ.trans hQ)
  have e1 : m = q ∘ₗ p := by
    ext x
    exact hm x
  have e2 : g.restrict (p := LinearMap.range g) (q := LinearMap.range g)
      (fun v _ => LinearMap.mem_range_self g v) = p ∘ₗ q := by
    ext x
    exact congrArg g (he (q x) (hWQ x.2)).symm
  rw [e1, LinearMap.trace_comp_comm', ← e2, hr]
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.IsotypicIntersectionProductEq

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_fix' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix' v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

theorem UpperTheory.isotypic_intersection_product_eq :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) → (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ κ : ℂ, ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (L i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (L i)) ((List.ofFn T).prod ∘L R) = κ * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI L hL hne
  obtain ⟨K, hK, hKL, hsK⟩ : ∃ K : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) ∧ (∀ i, K i ≤ L i) ∧
        ∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i := by
    refine ⟨fun i => L i ⊓ (L i).map ((s i).toMulEquiv : G i →* G i), fun i => ⟨?_, ?_⟩, fun i => inf_le_left, ?_⟩
    · have h2 : IsCompact (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (hL i).1.image (s i).continuous
      rw [Subgroup.coe_inf]
      exact (hL i).1.inter h2
    · have h2 : IsOpen (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (s i).toHomeomorph.isOpenMap _ (hL i).2
      rw [Subgroup.coe_inf]
      exact (hL i).2.inter h2
    · rintro i k ⟨-, y, hy, rfl⟩
      show (s i).symm (s i y) ∈ L i
      rw [(s i).symm_apply_apply]
      exact hy
  have hXX : (Z ⊓ ⨅ i, fixU (π i) (L i)) ≤ (Z ⊓ ⨅ i, fixU (π i) (K i)) := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j u hu =>
      (Submodule.mem_iInf _).1 h2 j u (hKL j hu)⟩
  haveI hfdX : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) := hadm K hK
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) := hadm L hL
  have hneX : (Z ⊓ ⨅ i, fixU (π i) (K i)) ≠ ⊥ := fun e => hne (le_bot_iff.1 (e ▸ hXX))
  obtain ⟨h1, c, hcc, hcf, hsp⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV K hK hfdX hneX
  obtain ⟨h1L, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV L hL hfdL hne
  haveI : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (K i)) := fun i => (h1 i).1
  have hLK : ∀ i, fixedVectors (τ i) (L i) ≤ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hx k (hKL i hk)
  have hIm : ∀ i, ∀ x ∈ fixedVectors (τ i) (L i), I i x ∈ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => by
      have h := hI i ((s i).symm k) x
      rw [(s i).apply_symm_apply, mem_fixedVectors.1 hx _ (hsK i k hk)] at h
      exact h.symm
  let e : ∀ i, fixedVectors (τ i) (K i) →ₗ[ℂ] S i := fun i =>
    (fixedVectors (τ i) (L i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 ∘ₗ (fixedVectors (τ i) (K i)).subtype
  let J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (((I i : S i →ₗ[ℂ] S i)) ∘ₗ e i).codRestrict (fixedVectors (τ i) (K i)) fun x =>
      hIm i _ (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x).2
  have he : ∀ i (x : fixedVectors (τ i) (K i)), (x : S i) ∈ fixedVectors (τ i) (L i) → e i x = x := fun i x hx =>
    fixedProj_apply_of_mem (hsm i) (hL i).1 (hL i).2 hx
  have hJ0 : ∀ i, J i ≠ 0 := fun i h0 => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h1L i).2
    have h := LinearMap.congr_fun h0 ⟨x, hLK i hx⟩
    have h' : I i (e i ⟨x, hLK i hx⟩) = 0 := congrArg Subtype.val h
    rw [he i ⟨x, hLK i hx⟩ hx] at h'
    exact hx0 ((I i).map_eq_zero_iff.1 h')
  obtain ⟨ρ, hρ1, hρ2⟩ := UpperTheory.isotypic_submodule_product_decomposition r G H S π τ Z hsm hcm hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J
    (fun i x => rfl) hcf hsp
  obtain ⟨κ, hκ⟩ := UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras r ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) (fun i => fixedVectors (τ i) (K i)) c J ρ hcc hJ0 hρ2
  refine ⟨κ, fun T A t hT1 hT2 hT3 hT4 hA ht => ?_⟩
  let B : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (A i ∘ₗ (fixedVectors (τ i) (K i)).subtype).codRestrict (fixedVectors (τ i) (K i)) fun x => hLK i (hA i _)
  have hcomp := UpperTheory.isotypic_subspace_product_closed r G H S π τ Z K c T B hcf hsp (fun i f hf x => hT4 i f hf x)
  have hPrZ : ∀ v ∈ Z, (List.ofFn fun j => prj (fixU (π j) (L j))).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hcm i j hij)).1 h v)
  have hTZ := UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L T hT1 hT2 hT3
  have hPrFix : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)), (List.ofFn fun j => prj (fixU (π j) (L j))).prod v = v := fun v hv =>
    prod_fix' v _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.1 v
        ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hv).2 i)
  let W : H →L[ℂ] H := (List.ofFn T).prod ∘L R ∘L (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have e1 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (K i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).1
    ((List.ofFn fun i => c i (B i)).prod * ρ) fun v => by
      rw [Module.End.mul_apply, hcomp, hρ1]
      rfl
  have hWX : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (K i)), W v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := fun v hv =>
    hTZ _ (hRZ _ (Submodule.mem_inf.1 (hPrZ v (Submodule.mem_inf.1 hv).1)).1)
  have e2 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).2 hXX hWX
  let b : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    ((W : H →ₗ[ℂ] H) ∘ₗ (Z ⊓ ⨅ i, fixU (π i) (L i)).subtype).codRestrict _ fun v => hWX _ (hXX v.2)
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i)) W).1 b fun v => rfl
  have e4 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i))
    ((List.ofFn T).prod ∘L R)).1 b fun v => by
      show W v = _
      show (List.ofFn T).prod (R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (v : H))) = _
      rw [hPrFix _ v.2]
      rfl
  have ht' : ∀ i, LinearMap.trace ℂ (fixedVectors (τ i) (K i)) (B i * J i) = t i := fun i =>
    UpperTheory.trace_restrict_eq_of_hasFinTrace (S i) (fixedVectors (τ i) (L i)) (fixedVectors (τ i) (K i)) (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)
      (B i * J i) (e i) (hLK i) (ht i) (fun x => hA i _) (fun x => rfl) (he i)
  rw [e4, ← e3, ← e2, e1, hκ B]
  simp only [ht']
end
end
