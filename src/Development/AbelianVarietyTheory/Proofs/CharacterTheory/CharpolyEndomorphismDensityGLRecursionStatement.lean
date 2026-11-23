module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMulParabolicInductionTrivialStatement
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassOfCharpolyCardCyclicVectors

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.CyclicMass

variable {F : Type} [Field F]

theorem charpoly_mulLeft_root (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)
  rw [AdjoinRoot.powerBasis'_gen] at h
  have h2 : minpoly F (AdjoinRoot.root D) = D := by
    rw [AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]; simp
  rw [h2] at h
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]
  exact h

theorem map_mk {V : Type} [AddCommGroup V] [Module F V] (D : F[X]) (f : AdjoinRoot D →ₗ[F] V)
    (g : Module.End F V) (h : ∀ a, f (AdjoinRoot.root D * a) = g (f a)) (p : F[X]) :
    f (AdjoinRoot.mk D p) = aeval g p (f 1) := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this, map_smul]; simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X, h, ih, map_mul (aeval g) X, aeval_X, Module.End.mul_apply]

theorem cyclic_one (D : F[X]) (U : Submodule F (AdjoinRoot D))
    (hU : ∀ a ∈ U, AdjoinRoot.root D * a ∈ U) (h1 : (1 : AdjoinRoot D) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]; exact U.smul_mem _ h1
  | add p q hp hq => rw [map_add (f := _)]; exact U.add_mem (hp trivial) (hq trivial)
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X]
    exact hU _ (ih trivial)

theorem card_pairs {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  let Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := fun e =>
    ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by
        rw [LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,
      ⟨e 1, fun U hU h1 => by
        have := cyclic_one D (U.comap e.toLinearMap) (fun a ha => by
          have := hU _ ha
          simpa [LinearEquiv.conj_apply] using this) h1
        rw [eq_top_iff]
        intro v _
        have h2 : e.symm v ∈ U.comap e.toLinearMap := this ▸ Submodule.mem_top
        simpa using h2⟩⟩
  have hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]),
      e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1 := fun e p =>
    map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · intro e e' h
    ext a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hΦ, hΦ, h]
  · rintro ⟨⟨g, hg⟩, ⟨v, hv⟩⟩
    have h0 : aeval g D = 0 := hg ▸ LinearMap.aeval_self_charpoly g
    let f : AdjoinRoot D →ₗ[F] V :=
      (LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD
    have hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v := fun p => by
      simp [f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]
    have hf1 : f 1 = v := by simpa using hf 1
    have hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a) := fun a => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← AdjoinRoot.mk_X, ← map_mul, hf, hf]; simp
    have hs : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine hv _ ?_ ⟨1, hf1⟩
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hfx a⟩
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs
    refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
    have hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩ := by
      apply Subtype.ext
      ext w
      obtain ⟨a, rfl⟩ := (LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w
      simp only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hfx a
    refine Sigma.ext hg' ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 hf1
    intro w
    rw [hg']

end GlobalTheory.CuspGL.CyclicMass

namespace GlobalTheory.CuspGL

theorem mass_card_cyclic (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  classical
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  have h := CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)
  haveI : Finite (Module.End F (Fin D.natDegree → F)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}
  rw [Nat.card_sigma] at h
  let e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hA])
  have h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F) := by
    refine Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)
    exact ⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩
  rw [glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]
  exact finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _

end GlobalTheory.CuspGL
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassOfCharpolyCardCyclicVectorsStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors : ∀ (F : Type) [Field F] [Finite F] (D : F[X]), D.Monic → mass (fun g : Module.End F (Fin D.natDegree → F) => (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F), (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  first | exact @GlobalTheory.CuspGL.mass_card_cyclic | exact GlobalTheory.CuspGL.mass_card_cyclic | (intros; apply GlobalTheory.CuspGL.mass_card_cyclic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumCardCyclicVectorsInvariantSubspaces

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_card_cyclic_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _
  have key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1),
      (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) →
      (v : V) ∈ W'.1 → W.1 ≤ W'.1 := by
    intro W W' v hv hv' x hx
    have h := hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'
    have : (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype := h ▸ Submodule.mem_top
    exact this
  let f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V := fun p => (p.2.1 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨W, v, hv⟩ ⟨W', v', hv'⟩ h
      have h' : (v : V) = v' := h
      have hW : W = W' := Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2))
        (key W' W v' hv' (h' ▸ v.2)))
      subst hW
      have : v = v' := Subtype.ext h'
      subst this
      rfl
    · intro v
      let S : Set (Submodule F V) := {U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}
      have hinv : ∀ x ∈ sInf S, g x ∈ sInf S := by
        intro x hx
        rw [Submodule.mem_sInf] at hx ⊢
        exact fun p hp => hp.1 x (hx p hp)
      have hv : v ∈ sInf S := by
        rw [Submodule.mem_sInf]
        exact fun p hp => hp.2
      refine ⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩
      intro U hU hvU
      have hle : sInf S ≤ U.map (sInf S).subtype := by
        refine sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨_, hU y hy, rfl⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)] at hc
  rw [finsum_eq_sum_of_fintype]
  exact_mod_cast hc

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumCardCyclicVectorsInvariantSubspacesStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V), ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, (Nat.card {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ) = (Nat.card F : ℂ) ^ Module.finrank F V := by
  first | exact @GlobalTheory.CuspGL.finsum_card_cyclic_eq | exact GlobalTheory.CuspGL.finsum_card_cyclic_eq | (intros; apply GlobalTheory.CuspGL.finsum_card_cyclic_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursion

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem cyclic_conj {F : Type} [Field F] {V V' : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] (e : V ≃ₗ[F] V') (g : Module.End F V) (v : V) :
    (∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤) ↔
      (∀ U : Submodule F V', (∀ x ∈ U, (e.conj g) x ∈ U) → e v ∈ U → U = ⊤) := by
  constructor
  · intro h U hU hv
    have h1 : U.comap (e : V →ₗ[F] V') = ⊤ := by
      refine h _ (fun x hx => ?_) hv
      have := hU (e x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e.symm y ∈ U.comap (e : V →ₗ[F] V') := h1 ▸ Submodule.mem_top
    simpa using this
  · intro h U hU hv
    have h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤ := by
      refine h _ (fun x hx => ?_) (by simpa using hv)
      have := hU (e.symm x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e y ∈ U.comap (e.symm : V' →ₗ[F] V) := h1 ▸ Submodule.mem_top
    simpa using this

theorem glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

theorem mass_const {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (c : ℂ) (P : F[X]) :
    mass (fun _ : Module.End F V => c) P = c * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  unfold mass
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V))
    DFunLike.coe_injective
  have hs : {g : Module.End F V | LinearMap.charpoly g = P}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  simp [mul_comm]

theorem mu_one (F : Type) [Field F] : mu (1 : F[X]) = 1 := by
  unfold mu
  have h : ∀ n : ℕ, n = 0 →
      mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1 := by
    rintro n rfl
    have h1 : glCard F 0 = 1 := by
      unfold glCard
      haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_unique]
      simp
    have h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0} := by
      ext g
      have hg : g = 0 := Subsingleton.elim _ _
      have hc : LinearMap.charpoly g = 1 := by
        apply (LinearMap.charpoly_monic g).natDegree_eq_zero.1
        rw [LinearMap.charpoly_natDegree]
        simp
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun _ => hg, fun _ => hc⟩
    unfold mass
    rw [h1, h2, finsum_mem_singleton]
    simp
  exact h _ natDegree_one

theorem mu_rec : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic →
    (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  intro F _ _ P hP
  refine ⟨?_, mu_one F⟩
  have key := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin P.natDegree → F)
    (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ))
    (by
      intro V V' _ _ _ _ _ _ e g
      congr 1
      exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)
    P hP (by simp)
  simp only [GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces] at key
  rw [mass_const] at key
  have hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P
      = conv (fun _ => 1) mu P := by
    unfold conv
    refine finsum_mem_congr rfl fun x hx => ?_
    beta_reduce
    rw [GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]
  rw [← hr, ← key]
  unfold mu
  simp [mul_div_assoc]

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursionStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.charpolyEndomorphismDensityGL_recursion : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic → (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  first | exact @GlobalTheory.CuspGL.mu_rec | exact GlobalTheory.CuspGL.mu_rec | (intros; apply GlobalTheory.CuspGL.mu_rec <;> assumption)
end
end
