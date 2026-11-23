module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescentSubring

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem NumD.exists_descent_subring : ∀ (O F : Type) [CommRing O] [CommRing F] (io : O →+* F), Function.Injective io → ∀ (N : NumD F) (A₀ : Subgroup N.A), (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, ∃ a : Oˣ, io a = N.θ x y u) → (∀ x ∈ A₀, ∃ a : Oˣ, io a = N.σ x) → (∀ x ∈ A₀, ∃ a : O, io a = N.th x) → (∀ χ, ∃ a : Oˣ, io a = N.ψ χ) → ∃ (N₀ : NumD O) (I : NumD.Hom io N₀ N), I.lam = 1 ∧ ∀ (k : ℕ) (p : N.QT k), p.1.2.b ∈ A₀ → (∀ χ, ∃ a : Oˣ, io a = p.1.2.s χ) → ∃ p₀ : N₀.QT k, p.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p.1.2 := by
  intro O F _ _ io hio N A₀ hc hθ hσ hth hψ
  have hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u := fun x y u =>
    (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h
  have hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x := fun x =>
    (hσ x x.2).imp fun a h => Units.ext h
  have hth' : ∀ x : A₀, ∃ a : O, io a = N.th x := fun x => hth x x.2
  have hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ := fun χ =>
    (hψ χ).imp fun a h => Units.ext h
  choose θ eθ using hθ'
  choose σ eσ using hσ'
  choose th eth using hth'
  choose ψ eψ using hψ'
  have inj : Function.Injective (Units.map io.toMonoidHom) := Units.map_injective hio
  let B₀ : NumB O :=
    { A := A₀
      θ := θ
      cub :=
        { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _)
          s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _)
          s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _)
          coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; exact N.cub.coc _ _ _ _) }
      σ := σ
      σ_one := inj (by rw [eσ, map_one]; exact N.σ_one)
      σ_mul := fun x y => inj (by simp only [map_mul, eθ, eσ]; exact N.σ_mul _ _)
      th := th }
  let N₀ : NumD O :=
    { toNumB := B₀
      X := N.X
      c := fun χ => (⟨N.c χ, hc χ⟩ : A₀)
      c_add := fun a b => Subtype.ext (N.c_add a b)
      ψ := ψ
      even := fun χ => inj (by
        change Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _
        simp only [map_mul, eψ, eσ]; exact N.even χ)
      bimult := fun a a' b => inj (by
        change Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _
        simp only [map_mul, map_div, eψ, eθ]; exact N.bimult a a' b) }
  let I : NumD.Hom io N₀ N :=
    { φ := A₀.subtype
      h := fun _ => 1
      h_one := rfl
      θ_eq := fun (x y u : A₀) => by
        simp only [mul_one]; exact (eθ x y u).symm
      σ_eq := fun (x : A₀) => by
        simp only [mul_one]; exact (eσ x).symm
      lam := 1
      th_eq := fun (x : A₀) => by
        simp only [mul_one, Units.val_one, one_mul]; exact (eth x).symm
      e := AddEquiv.refl N.X
      c_eq := fun _ => rfl
      ψ_eq := fun (χ : N.X) => by
        simp only [mul_one]; exact (eψ χ).symm }
  let Φ : N₀.Gt →* N.Gt := MonoidHom.mk'
    (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by
      have := congrArg (Units.map io.toMonoidHom) (g.mult χ χ')
      rw [map_mul, map_mul] at this
      rw [← this]
      exact congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)
    (fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _
      rw [map_div, map_mul, eθ]; rfl))
  have Φinj : Function.Injective Φ := fun g g' h =>
    NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h))
      (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))
  have Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y := fun y =>
    NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _
      rw [map_div, map_div, eψ, eψ, eψ]; rfl)
  refine ⟨N₀, I, rfl, fun k p hb hs => ?_⟩
  have hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ := fun χ =>
    (hs χ).imp fun a h => Units.ext h
  choose s es using hs'
  let g₀ : N₀.Gt := ⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by
    change Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _
    simp only [map_mul, es, eθ]; exact p.1.2.mult χ χ')⟩
  have hg : Φ g₀ = p.1.2 := NumD.Gt.ext rfl (funext fun χ => es χ)
  refine ⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩
  · change Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))
    rw [map_pow, hg, Φio]; exact p.2
  · change p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1
    rw [es, mul_one, mul_one]

end GlobalTheory.Ex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebra

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.TorsDesc

theorem s_mem_of_basis {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ) (g : N.Gt) {ι : Type}
    (e : Module.Basis ι ℤ N.X) (hθ : ∀ χ χ', N.θ (N.c χ) (N.c χ') g.b ∈ U) (he : ∀ l, g.s (e l) ∈ U) (χ : N.X) :
    g.s χ ∈ U := by
  have hχ : χ ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; trivial
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact he l
  | zero => rw [NumD.Gt.s_zero]; exact U.one_mem
  | add x y _ _ hx hy =>
    rw [eq_div_iff_mul_eq'.2 (g.mult x y)]
    exact U.div_mem (U.mul_mem hx hy) (hθ _ _)
  | neg x _ hx =>
    have := g.mult x (-x)
    rw [add_neg_cancel, NumD.Gt.s_zero, one_mul] at this
    exact (U.mul_mem_cancel_left hx).1 (this ▸ hθ _ _)

theorem s_mem_of_root {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ)
    (hθ : ∀ x y u, N.θ x y u ∈ U) (hψ : ∀ χ, N.ψ χ ∈ U) {k : ℕ} (hU : ∀ u : Fˣ, u ^ k ∈ U → u ∈ U) (p : N.QT k)
    (χ : N.X) : p.1.2.s χ ∈ U := by
  refine hU _ ?_
  rw [← NumD.Gt.pow_s, N.mem_QT.1 p.2, NumD.io_s]
  exact U.mul_mem (U.div_mem (U.div_mem (hψ _) (hψ _)) (hψ _)) (U.prod_mem fun _ _ => hθ _ _ _)

theorem exists_finite_subalgebra (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F]
    (K : IntermediateField (FractionRing O) F) [FiniteDimensional (FractionRing O) K] :
    ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∀ x ∈ K, IsIntegral O x → x ∈ O₁ := by
  have : CharZero (FractionRing O) := IsFractionRing.charZero_of_isFractionRing O
  have : Module.Finite O (integralClosure O K) := IsIntegralClosure.finite O (FractionRing O) K _
  let v : K →ₐ[O] F := { K.val.toRingHom with commutes' := fun _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  refine ⟨(integralClosure O K).map v, Module.Finite.equiv ((integralClosure O K).equivMapOfInjective v hv).toLinearEquiv,
    fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff v hv).1 hi

theorem descend : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  intro O F _ _ _ _ _ _ _ _ _ _ S hS N K₁ A₀ hK hc hθ hσ hth hψ vθ vσ vth vψ Ix _ k p hk hp
  let e := Module.Free.chooseBasis ℤ N.X
  let T : Set F := Set.range fun il : Ix × Module.Free.ChooseBasisIndex ℤ N.X => ((p il.1).1.2.s (e il.2) : F)
  have : Finite T := (Set.finite_range _).to_subtype
  have : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K₂ := K₁ ⊔ IntermediateField.adjoin (FractionRing O) T
  have : FiniteDimensional (FractionRing O) K₂ := IntermediateField.finiteDimensional_sup _ _
  have h12 : K₁ ≤ K₂ := le_sup_left
  obtain ⟨O₁, hfin, hO⟩ := exists_finite_subalgebra O F K₂
  have hunit : ∀ u : Fˣ, (u : F) ∈ K₂ → S.valuation (u : F) = 1 → ∃ a : O₁ˣ, O₁.val.toRingHom a = u := by
    intro u hu hv
    have h1 : (u : F) ∈ O₁ := hO _ hu ((hS _).1 ((S.valuation_le_one_iff _).1 hv.le))
    have h2 : ((u⁻¹ : Fˣ) : F) ∈ O₁ := by
      rw [Units.val_inv_eq_inv_val]
      exact hO _ (K₂.inv_mem hu) ((hS _).1 ((S.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])))
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  let U : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ K₂}
      mul_mem' := fun ha hb => K₂.mul_mem ha hb
      one_mem' := K₂.one_mem
      inv_mem' := fun {u} hu => by
        change ((u⁻¹ : Fˣ) : F) ∈ K₂
        rw [Units.val_inv_eq_inv_val]
        exact K₂.inv_mem hu }
  let V : Subgroup Fˣ := (S.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom F)).ker
  obtain ⟨N₀, I, hI, h⟩ := GlobalTheory.Ex.NumD.exists_descent_subring O₁ F O₁.val.toRingHom Subtype.val_injective N A₀ hc
    (fun x hx y hy u hu => hunit _ (h12 (hθ x hx y hy u hu)) (vθ _ _ _))
    (fun x hx => hunit _ (h12 (hσ x hx)) (vσ _))
    (fun x hx => ⟨⟨_, hO _ (h12 (hth x hx)) ((hS _).1 (vth x))⟩, rfl⟩)
    (fun χ => hunit _ (h12 (hψ χ)) (vψ _))
  refine ⟨O₁, hfin, N₀, I, hI, fun i p' ⟨z, _, hz⟩ => h _ p' ?_ fun χ => hunit _ ?_ ?_⟩
  · rw [hz]
    exact A₀.mul_mem (hp i) (hc z)
  · have h1 : (p i).1.2.s χ ∈ U := s_mem_of_basis N U _ e (fun χ χ' => h12 (hθ _ (hc _) _ (hc _) _ (hp i)))
      (fun l => (le_sup_right : _ ≤ K₂) (IntermediateField.subset_adjoin _ _ ⟨(i, l), rfl⟩)) χ
    have hψU : ∀ χ, N.ψ χ ∈ U := fun χ => h12 (hψ χ)
    change p'.1.2.s χ ∈ U
    rw [hz, NumD.Gt.mul_s]
    exact U.div_mem (U.mul_mem h1 (U.div_mem (U.div_mem (hψU _) (hψU _)) (hψU _)))
      (h12 (hθ _ (hc _) _ (hp i) _ (hc z)))
  · refine s_mem_of_root N V vθ vψ (fun u hu => ?_) p' χ
    have : S.valuation (u : F) ^ k i = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val]; exact hu
    exact (pow_eq_one_iff_of_nonneg zero_le (hk i).ne').1 this

end GlobalTheory.Ex.TorsDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebraStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionClasses_descend_finite_algebra : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  first | exact @GlobalTheory.Ex.TorsDesc.descend | exact GlobalTheory.Ex.TorsDesc.descend | (intros; apply GlobalTheory.Ex.TorsDesc.descend <;> assumption)
end
end
