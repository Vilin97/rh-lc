module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Finiteness
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.WittInt

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ z ∈ Λ, P z ∈ Λ) ∧ (∀ z, P z ∈ W) ∧ ∀ z ∈ W, P z = z := by
  have hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ := fun y => by
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨s, hs⟩
  have hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨s, hs⟩ := hmul y
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W := fun s v h => by
    rw [← algebraMap_smul K] at h
    exact (W.smul_mem_iff (hne s)).1 h
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := (W.restrictScalars O).comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c v h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y
  refine ⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact (π _).2
  · obtain ⟨c, hc⟩ := hmul z
    refine hsat c _ ?_
    rw [← LinearMap.map_smul_of_tower]
    have := hg ⟨_, hc⟩
    rw [show g ((c : O) • z) = _ from this]
    exact hπ _
  · obtain ⟨c, hc⟩ := hmul z
    have h1 := hg ⟨_, hc⟩
    rw [hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)] at h1
    have h2 : g (algebraMap O K c • z) = algebraMap O K c • z := by
      rw [algebraMap_smul]; exact h1
    rw [map_smul] at h2
    exact smul_right_injective V (hne c) h2

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem form_star {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]

theorem form_adj {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    star (M *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ ((J⁻¹ * Mᴴ * J) *ᵥ y)) := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_nondeg {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (y : Fin n → E)
    (h : ∀ x : Fin n → E, star x ⬝ᵥ (J *ᵥ y) = 0) : y = 0 := by
  apply eq_zero_of_mulVec_eq_zero hd
  funext i
  have := h (Pi.single i 1)
  simpa [← Pi.single_star] using this

theorem exists_adjoint {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0)
    (P : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ Q : (Fin n → E) →ₗ[E] (Fin n → E),
      (∀ x y, star (P x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ Q y)) ∧
      LinearMap.trace E _ Q = star (LinearMap.trace E _ P) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective P
  refine ⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle,
    mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]

end Form

theorem split_of_trace (E : Type) [Field E] [NumberField E] [StarRing E] (w : 𝓞 E)
    (hw : (w : E) + star (w : E) = 1) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (hd : J.det ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hself : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (W : Submodule E (Fin n → E)) (hW : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) :
    ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧
      Module.finrank E W' = Module.finrank E W ∧
      (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧
      ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧
        ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  have hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
    let U := Submodule.span E (Λ : Set (Fin n → E))
    change U = ⊤
    by_contra hU
    let g : (Fin n → E) →ₗ[E] Module.Dual E U :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin J)).domRestrict₂ U
    have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hU
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := star z
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      have := congrArg star hy
      simpa [y] using this
    have hline (a : E) : a • y ∈ Λ := (hself _).2 fun x hx => by
      have hz' : z ⬝ᵥ (J *ᵥ x) = 0 :=
        congrArg (fun f : Module.Dual E U => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have horth : star x ⬝ᵥ (J *ᵥ y) = 0 := by
        rw [← form_star hJ y x]
        simp [y, hz']
      simp only [Matrix.mulVec_smul, dotProduct_smul, horth, smul_zero]
      exact ⟨0, map_zero _⟩
    let i : E →ₗ[𝓞 E] Λ :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict Λ hline
    let : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨P, hPΛ, hPW, hPid⟩ := exists_projector Λ hΛ.fg hspan W
  obtain ⟨Q, hPQ, htr⟩ := exists_adjoint hd P
  have hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y) := fun x y => by
    rw [← form_star hJ, ← hPQ, form_star hJ]
  have hQΛ : ∀ z ∈ Λ, Q z ∈ Λ := fun z hz => (hself _).2 fun y hy => by
    rw [← hPQ]; exact (hself z).1 hz _ (hPΛ y hy)
  have hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0 := fun y hy =>
    form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)
  have hQW : ∀ y ∈ W, Q y = 0 := fun y hy => hQ0 y fun x hx => hW x hx y hy
  have hPP : ∀ y, P (P y) = P y := fun y => hPid _ (hPW y)
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    rw [← sub_eq_zero]
    refine form_nondeg hd _ fun x => ?_
    rw [mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]
  have hQPz : ∀ y, Q (P y) = 0 := fun y => hQW _ (hPW y)
  let T : (Fin n → E) →ₗ[E] (Fin n → E) := Q - (w : E) • (P ∘ₗ Q)
  have hT : ∀ y, T y = Q y - (w : E) • P (Q y) := fun y => rfl
  have hQT : ∀ y, Q (T y) = Q y := fun y => by
    rw [hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]
  have hTT : ∀ y, T (T y) = T y := fun y => by rw [hT (T y), hQT, hT]
  have hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y) := fun x hx y => by
    rw [hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]
  have hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) =
      star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y))) := fun x y => by
    rw [hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub,
      dotProduct_sub, mulVec_smul, dotProduct_smul]
  refine ⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero,
      dotProduct_zero]
  · have h1 : LinearMap.IsProj W P := ⟨hPW, hPid⟩
    have h2 : LinearMap.IsProj (LinearMap.range T) T :=
      ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩
    have h3 : Q ∘ₗ P = 0 := LinearMap.ext hQPz
    have h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q := by
      simp only [T]
      rw [map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]
    rw [h2.trace, htr, h1.trace, star_natCast] at h4
    exact_mod_cast h4
  · rintro _ ⟨y, rfl⟩ hy
    have h0 : Q y = 0 := hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx
    rw [hT, h0, map_zero, smul_zero, sub_zero]
  · have hTz : T z ∈ Λ := Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))
    have hu : z - T z ∈ Λ := Λ.sub_mem hz hTz
    have hxW : P (z - T z) ∈ W := hPW _
    have hQu : Q (z - T z) = 0 := by rw [map_sub, hQT, sub_self]
    refine ⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self,
      sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub,
      mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, sub_self, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ W : Submodule E (Fin n → E), (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧ Module.finrank E W' = Module.finrank E W ∧ (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧ ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  intro E _ _ _ hE n J hJ hd Λ hΛ hs W hW
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one E hE
  exact split_of_trace E w hw n J hJ hd Λ hΛ hs W hW

end GlobalTheory.WittInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  obtain ⟨xΛ, hxΛ⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ hΛ (by simpa only [hform_eq] using hdual)
  have hΛfull : Submodule.IsFullLattice I.E Λ :=
    { toIsLattice := hΛ
      span_eq_top := by rw [← hxΛ]; exact (GlobalTheory.PointLattice.lamX_selfDual I (1, xΛ)).2.2.1 }
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛfull hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL.toIsLattice, hLd⟩
    ⟨I₀.L, Submodule.IsLattice.of_fg I₀.E I₀.L_fg, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛfull hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL'.toIsLattice (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      have hsp := Submodule.IsFullLattice.span_eq_top (self := hΛ i)
      exact this (hsp ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    (Submodule.IsLattice.of_fg I.E hfg) hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ (Submodule.IsLattice.of_fg I.E hfg) hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlagStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  first | exact @GlobalTheory.AdaptedExists.exists_isAdapted | exact GlobalTheory.AdaptedExists.exists_isAdapted | (intros; apply GlobalTheory.AdaptedExists.exists_isAdapted <;> assumption)
end
end
