module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivations

section

@[expose] public section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivationsStatement

section

@[expose] public section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  first | exact @GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | exact GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | (intros; apply GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationComm

section

@[expose] public section

set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationCommStatement

section

@[expose] public section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhd

section

@[expose] public section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations (Hol (K.W k)) (dw a) (dw b) (GlobalTheory.T.fibreCoordinatePartialDerivation_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (K.sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (K.sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (K.sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosed

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.ClosedSq

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)

theorem diff (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k))
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (hn : ∀ a, n a ∈ T.J) (hnn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.fst : Hol (K.W k)) + ∑ a, f₁.φ (θ.snd a : Hol (K.W k)) * n a := by
  obtain ⟨χ, hd, h0, h1, hχ⟩ := exists_jet_factor K f₁ f₂ n (d₁.trans d₂.symm) hn hnn hf
  have e0 := hh _ _ _ (jet0 k) χ rfl (hd.trans d₁)
  have e1 := hh _ _ _ (jet1 k) χ rfl (hd.trans d₁)
  rw [h0] at e0
  rw [h1] at e1
  rw [← hχ θ, hθ, h₁, h₂, e0, e1]
  exact (add_sub_add_right_eq_sub _ _ _).trans (map_sub χ.φ _ _).symm

theorem sum_single {O : Type} [CommRing O] (v : Fin g → O) (a : Fin g) (e : O) :
    ∑ c, v c * (Pi.single a e : Fin g → O) c = v a * e := by
  simp [Pi.single_apply]

theorem diff1 (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k)) (h0 : θ.fst = 0)
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (a : Fin g) (e : T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (he : e ∈ T.J) (hee : e * e = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + f₁.φ (dw a x : Hol (K.W k)) * e) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.snd a : Hol (K.W k)) * e := by
  have := diff K h hh k θ hθ f₁ f₂ (Pi.single a e) d₁ d₂
    (fun c ↦ by rw [Pi.single_apply]; split_ifs; exacts [he, T.J.zero_mem])
    (fun c d ↦ by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      exacts [hee, mul_zero _, zero_mul _, mul_zero _])
    (fun x ↦ (hf x).trans (congrArg (f₁.φ x + ·) (sum_single (fun c ↦ f₁.φ (dw c x : Hol (K.W k))) a e).symm)) u₁ u₂ h₁ h₂
  rw [this, h0, sum_single (fun c ↦ f₁.φ (θ.snd c : Hol (K.W k)))]
  exact (congrArg (· + _) (map_zero f₁.φ)).trans (zero_add _)

theorem units_mul_relation_rearrange_commRing {C : Type} [CommRing C] (u₀ u₁ u₂ u₃ A B A' B' A₂ B₁ e₁ e₂ : C) (h1 : u₀ - u₁ = A * e₁)
    (h2 : u₁ - u₃ = B₁ * e₂) (h3 : u₀ - u₂ = B * e₂) (h4 : u₂ - u₃ = A₂ * e₁) (h5 : B₁ = B + B' * e₁)
    (h6 : A₂ = A + A' * e₂) : (B' - A') * e₁ * e₂ = 0 := by
  subst h5 h6
  linear_combination -h1 - h2 + h3 + h4

theorem connForm_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  intro I _ g Λ _ F K h hh k θ hθ
  have h0 : θ.fst = 0 := by
    have := diff K h hh k θ hθ (𝟙 (K.triv k)) (𝟙 (K.triv k)) (fun _ ↦ 0) rfl rfl (fun _ ↦ (K.triv k).J.zero_mem)
      (fun _ _ ↦ mul_zero _) (fun x ↦ by simp only [mul_zero, Finset.sum_const_zero, add_zero]) _ _ rfl rfl
    simp only [mul_zero, Finset.sum_const_zero, add_zero, sub_self] at this
    exact this.symm
  refine ⟨h0, fun a b ↦ ?_⟩
  obtain ⟨T, φ₀, φ₁, φ₂, φ₃, e₁, e₂, d₀, d₁, d₂, d₃, m₁, m₂, s₁, s₂, p₁, p₂, p₃, p₄, inj⟩ :=
    exists_second_order_nbhd I g Λ F K k a b
  refine sub_eq_zero.1 (inj _ ?_)
  have := units_mul_relation_rearrange_commRing _ _ _ _ _ _ _ _ _ _ e₁ e₂
    (diff1 K h hh k θ hθ h0 φ₀ φ₁ a e₁ d₀ d₁ m₁ s₁ p₁ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₁ φ₃ b e₂ d₁ d₃ m₂ s₂ p₃ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₀ φ₂ b e₂ d₀ d₂ m₂ s₂ p₂ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₂ φ₃ a e₁ d₂ d₃ m₁ s₁ p₄ _ _ rfl rfl) (p₁ _) (p₂ _)
  exact (congrArg (· * e₁ * e₂) (map_sub φ₀.φ _ _)).trans this

end GlobalTheory.AnPer.ClosedSq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormDegZeroCocycleClosedStatement

section

@[expose] public section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  first | exact @GlobalTheory.AnPer.ClosedSq.connForm_closed | exact GlobalTheory.AnPer.ClosedSq.connForm_closed | (intros; apply GlobalTheory.AnPer.ClosedSq.connForm_closed <;> assumption)
end
end
