module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.Fourier

section

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.fourier :
    ∀ (K Q : Type) [Field K] [IsAlgClosed K] [CharZero K] [CommGroup Q] [Finite Q] (a : MonoidAlgebra K Q), (∀ χ : Q →* Kˣ, MonoidAlgebra.lift K K Q ((Units.coeHom K).comp χ) a = 0) → a = 0 := by
  intro K Q _ _ _ _ _ a h
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent Q : ℕ) : K) := ⟨by exact_mod_cast NeZero.ne (Monoid.exponent Q)⟩
  let ev : Q → ((Q →* Kˣ) →* K) := fun q =>
    { toFun := fun χ => (χ q : K), map_one' := by simp, map_mul' := fun x y => by simp }
  have hinj : Function.Injective ev := by
    intro q q' hq
    refine (CommGroup.forall_apply_eq_apply_iff Q (M := K)).1 fun φ => ?_
    exact Units.ext (DFunLike.congr_fun hq φ)
  have hli := (linearIndependent_monoidHom (Q →* Kˣ) K).comp ev hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun q => a.coeff q) (by
    funext χ
    have := h χ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [ev, Finset.sum_apply] using this)
  ext q
  simpa using key q
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistOf

section

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.isTwistOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] (x x' : B.B →+* R) (γ : F.G₀ →* Rˣ), TwMap B x x' γ → (B.u.D.map x).IsTwist γ (B.u.D.map x') := by
  intro l _ F O _ _ _ n r B R _ x x' γ h
  have hmap (f : B.B →+* R) : ∀ i g, (B.u.D.map f).lam i (MonoidAlgebra.single g 1) =
      f (B.u.D.lam i (MonoidAlgebra.single g 1)) := by
    have hchi : ∀ y, (B.u.D.map f).chi (MonoidAlgebra.mapRingHom F.G₀ f y) = (B.u.D.chi y).map f := by
      intro y
      have he : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C (MonoidAlgebra.mapRingHom F.G₀ f y) =
          MonoidAlgebra.mapRingHom F.G₀ (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (B.u.D.map f).D R[X] _ = _
      rw [he]
      let : Algebra B.B R[X] := ((algebraMap R R[X]).comp f).toAlgebra
      have hc : ∀ a : B.B, Polynomial.mapRingHom f (algebraMap B.B B.B[X] a) = algebraMap B.B R[X] a := by
        intro a
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f
      exact B.u.D.nat B.B[X] R[X] { Polynomial.mapRingHom f with commutes' := hc } _
    have hm : ∀ i y, (B.u.D.map f).lam i (MonoidAlgebra.mapRingHom F.G₀ f y) = f (B.u.D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    intro i g
    simpa using hm i (MonoidAlgebra.single g 1)
  have e : B.u.D.map x' = twD (B.u.D.map x) γ := by
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ hi => ?_
    have s : MonoidAlgebra.single g ((1 : R) * algebraMap R R (γ g)) =
        (γ g : R) • MonoidAlgebra.single g (1 : R) := by
      simp
    rw [lam_twD, twA_single, s, lamSmul, min_eq_left hi, hmap x, hmap x']
    exact h.1 g i hi
  rw [e]
  exact isTwist_twD _ _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LevelJ

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem lift_map {A K Q : Type} [CommRing A] [CommRing K] [CommGroup Q] (x : A →+* K) (χ : Q →* K) :
    ∃ e : MonoidAlgebra A Q →+* K, (∀ a, e (algebraMap A _ a) = x a) ∧ (∀ z, e (MonoidAlgebra.single z 1) = χ z) ∧
      ∀ y, e y = MonoidAlgebra.lift K K Q χ (MonoidAlgebra.mapRingHom Q x y) := by
  refine ⟨(MonoidAlgebra.lift K K Q χ).toRingHom.comp (MonoidAlgebra.mapRingHom Q x), ?_, ?_, fun y => rfl⟩
  · intro a
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]
  · intro z
    simp [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Ws.H5.levelJ :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), B.Dense J → B.TwistOk J → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∀ q : V.frame.G₀ →* Q, IsOpen (q.ker : Set V.frame.G₀) → Anti V.frame q → ∀ tw : B.B →ₐ[c.O] MonoidAlgebra B.B Q, TwMap B (algebraMap B.B (MonoidAlgebra B.B Q)) (tw : B.B →+* MonoidAlgebra B.B Q) ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) → ∀ b ∈ J, ∀ z : Q, (tw b).coeff z ∈ J := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B J hD hT Q _ _ hQ q hq hA tw htw b hb z
  let h0 : s.Wt n := fun _ j _ => (j : ℤ)
  have hinc : h0.Incr := by
    intro v τ a a' hlt
    show ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ)
    exact_mod_cast hlt
  refine hD h0 hinc _ ?_
  intro x hxJ hxG
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := l) (G := Q)).1 hQ
  have hzero : MonoidAlgebra.mapRingHom Q (x : B.B →+* Qbar l) (tw b) = 0 := by
    apply Ws.H5.fourier (Qbar l) Q
    intro χ
    obtain ⟨e, he1, he2, he3⟩ := lift_map (x : B.B →+* Qbar l) ((Units.coeHom (Qbar l)).comp χ)
    rw [← he3]
    let β : V.frame.G₀ →* (Qbar l)ˣ := χ.comp q
    let x' : B.Pt :=
      { toRingHom := e.comp (tw : B.B →+* MonoidAlgebra B.B Q)
        commutes' := by
          intro o
          show e (tw (algebraMap c.O B.B o)) = algebraMap c.O (Qbar l) o
          rw [tw.commutes, IsScalarTower.algebraMap_apply c.O B.B (MonoidAlgebra B.B Q), he1]
          exact x.commutes o }
    have hker : q.ker ≤ β.ker := by
      intro g hg
      rw [MonoidHom.mem_ker] at hg ⊢
      show χ (q g) = 1
      rw [hg, map_one]
    have htw' : TwMap B (x : B.B →+* Qbar l) (x' : B.B →+* Qbar l) β := by
      have h2 := htw.comp e
      have ea : e.comp (algebraMap B.B (MonoidAlgebra B.B Q)) = (x : B.B →+* Qbar l) := by
        ext a
        exact he1 a
      have eb : pushCh e ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) = β := by
        ext g
        exact he2 (q g)
      rw [ea, eb] at h2
      exact h2
    have hx'J : J ≤ RingHom.ker (x' : B.B →+* Qbar l) := by
      refine hT x x' h0 β hxJ hxG (Subgroup.isOpen_mono hker hq) ⟨k, ?_⟩ ?_ ?_ ?_ ?_ ?_
      · ext g
        show (χ (q g) ^ l ^ k : (Qbar l)ˣ).1 = 1
        rw [← map_pow, ← hk, pow_card_eq_one', map_one]
        rfl
      · ext g
        show (χ (q (V.frame.conj g)) : Qbar l) = ((χ (q g))⁻¹ : (Qbar l)ˣ)
        rw [eq_inv_of_mul_eq_one_left (hA.conj g), map_inv]
      · intro u
        exact (hA.iu u).trans hker
      · exact hA.i0.trans hker
      · exact isTwistOf B _ _ β htw'
      · intro v j
        ext g
        show e (tw ((B.u.ψ v j g : (B.B)ˣ) : B.B)) = x ((B.u.ψ v j g : (B.B)ˣ) : B.B) * (χ (q (V.pr (g : G L Ω))) : Qbar l)
        refine (congrArg e (htw.2 v j g)).trans ?_
        rw [map_mul, he1]
        congr 1
        exact he2 _
    exact hx'J hb
  have := congrArg (fun y => y.coeff z) hzero
  simp only [MonoidAlgebra.mapRingHom_apply] at this
  exact this
end
end
