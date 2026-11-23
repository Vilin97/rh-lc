module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOneStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacter

section

@[expose] public section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem nonempty_piTensor_detRep_equiv (R β : Type) [CommRing R] [Fintype β] (c : β → Type)
    [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) :
    Nonempty ((piTensor fun j => detRep (c j) (χ j)).Equiv (ofChar (leviChar c χ))) := by
  classical
  refine ⟨LocGL.equivOfBijective
    ⟨(PiTensorProduct.constantBaseRingEquiv β ℂ).toLinearMap, fun g => ?_⟩
    (PiTensorProduct.constantBaseRingEquiv β ℂ).bijective⟩
  ext x
  simp [leviChar_apply, detRep, Finset.prod_mul_distrib]

end GlobalTheory.SmGL.Exponents
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv

section

@[expose] public section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankOneProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)]


omit [Fintype α] [LinearOrder α] [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem isEmpty_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) : IsEmpty (c a) :=
  ⟨fun x => ha (congrArg Sigma.fst (g.injective (Subsingleton.elim (g ⟨a, x⟩) (g (g.symm ())))))⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in
theorem det_eq_one_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) (x : GL (c a) k) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have := isEmpty_of_ne g ha
  ext
  simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α]
  [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem mem_parab_unit (g : (Σ i, c i) ≃ Unit) (x : GL Unit k) : x ∈ parab k g :=
  by
    change Matrix.BlockTriangular (x : Matrix Unit Unit k) (blk g)
    intro i j h
    cases i
    cases j
    exact absurd h (lt_irrefl _)

theorem deltaHalf_eq_one (g : (Σ i, c i) ≃ Unit) (x : Levi k c) : deltaHalf k c x = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = (g.symm ()).1
  · have h : modExp c a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne)
        simp
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne')
        simp
    simp [h]
  · rw [det_eq_one_of_ne g ha, map_one]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_leviProj (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ) (p : parab k g)
    (w : PiTensorProduct ℂ fun _ : α => ℂ) :
    piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p) w =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) • w := by
  have hd : (∏ a, (detChar (c a) (ψ a) (leviProj k g p a) : ℂ)) =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) := by
    rw [Finset.prod_eq_single (g.symm ()).1, detChar_apply, detChar_apply, det_parab,
      Finset.prod_eq_single (g.symm ()).1]
    · intro b _ hb
      exact det_eq_one_of_ne g hb _
    · simp
    · intro b _ hb
      rw [detChar_apply, det_eq_one_of_ne g hb, map_one, Units.val_one]
    · simp
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod, ← hd, smul_comm]
    congr 1
    calc
      _ = (PiTensorProduct.tprod ℂ) (fun a => (detChar (c a) (ψ a) (leviProj k g p a) : ℂ) • x a) := by rfl
      _ = _ := MultilinearMap.map_smul_univ _ _ _

theorem nonempty_equiv_multiProd_unit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type)
    [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) :
    Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  let L : (PiTensorProduct ℂ fun _ : α => ℂ) ≃ₗ[ℂ] ℂ :=
    (PiTensorProduct.constantBaseRingEquiv α ℂ).toLinearEquiv
  have law : ∀ (φ : IndSp g (piTensor fun i => detRep (c i) (ψ i))) (x : GL Unit k),
      φ.1.1 x = (detChar Unit (ψ (g.symm ()).1) x : ℂ) • φ.1.1 1 := fun φ x => by
    have := parInd_law g _ φ ⟨x, mem_parab_unit g x⟩ 1
    rw [deltaHalf_eq_one g, piTensor_leviProj, mul_one, Units.val_one, one_smul] at this
    exact this
  let f : IndSp g (piTensor fun i => detRep (c i) (ψ i)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => L (φ.1.1 1)
      map_add' := fun φ φ' => map_add L _ _
      map_smul' := fun r φ => map_smul L r _ }
  refine ⟨LocGL.equivOfBijective ⟨f, fun x => LinearMap.ext fun φ => ?_⟩ ⟨fun φ φ' h => ?_, fun z => ?_⟩⟩
  · show L (φ.1.1 (1 * x)) = detRep Unit (ψ (g.symm ()).1) x (L (φ.1.1 1))
    rw [one_mul, law, map_smul]
    exact (ofChar_apply _ _ _).symm
  · have h1 : φ.1.1 1 = φ'.1.1 1 := L.injective h
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [law φ x, law φ' x, h1]
  · refine ⟨⟨⟨fun x => (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z, fun p x => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds ((hψ (g.symm ()).1).detChar (n := Unit)) (one_mem _)) fun y hy => ?_)⟩, ?_⟩
    · show (detChar Unit (ψ (g.symm ()).1) (p * x) : ℂ) • L.symm z =
        (deltaHalf k c (leviProj k g p) : ℂ) • piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p)
          ((detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z)
      rw [deltaHalf_eq_one g, piTensor_leviProj, Units.val_one, one_smul, map_mul, Units.val_mul,
        mul_smul]
    · have hy' : detChar Unit (ψ (g.symm ()).1) y = 1 := hy
      apply Subtype.ext
      funext x
      show (detChar Unit (ψ (g.symm ()).1) (x * y) : ℂ) • L.symm z =
        (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z
      rw [map_mul, hy', mul_one]
    · show L ((detChar Unit (ψ (g.symm ()).1) 1 : ℂ) • L.symm z) = z
      rw [map_one, Units.val_one, one_smul, L.apply_symm_apply]

end GlobalTheory.SmGL.RankOneProduct
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquivStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityLeviCharGeometricLemmaCe

section

@[expose] public section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem leviChar_unit_injective {R β : Type} [CommRing R] [Fintype β] {χ ψ : β → Rˣ →* ℂˣ}
    (h : leviChar (fun _ : β => Unit) χ = leviChar (fun _ : β => Unit) ψ) : χ = ψ := by
  classical
  funext j
  ext1 x
  have key : ∀ φ : β → Rˣ →* ℂˣ, leviChar (fun _ : β => Unit) φ
      (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar Unit x)) = φ j x := by
    intro φ
    rw [leviChar_apply, Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
      congr 1
      ext
      simp
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
    · simp
  rw [← key χ, ← key ψ, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_leviChar_of_smooth {β : Type} [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] {χ : β → kˣ →* ℂˣ} (h : ∀ j, IsSmoothChar (χ j)) :
    IsSmoothChar (leviChar c χ) := by
  unfold leviChar
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one
    fun a _ => ?_
  exact (h a).detChar.comp _ (continuous_apply a)

theorem nonempty_cell_term_equiv {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (g : ∀ j, (Σ i, c i j) ≃ Unit) (s : ∀ i j, IrrRep (GL (c i j) k)) (ψ : α → β → kˣ →* ℂˣ)
    (hψ : ∀ i j, IsSmoothChar (ψ i j)) (e : ∀ i j, Nonempty ((s i j).ρ.Equiv (detRep (c i j) (ψ i j)))) :
    Nonempty ((piTensor fun j => multiProd (g j) fun i => (s i j).ρ).Equiv
      (ofChar (leviChar (fun _ : β => Unit) fun j => ψ ((g j).symm ()).1 j))) := by
  obtain ⟨a⟩ := nonempty_piTensor_detRep_equiv k β (fun _ => Unit) fun j => ψ ((g j).symm ()).1 j
  refine ⟨Representation.Equiv.trans (LocGL.piTensorEquiv fun j => ?_) a⟩
  exact (LocGL.multiProdEquiv (g j) fun i => (e i j).some).trans
    (GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv k α (fun i => c i j) (g j) (fun i => ψ i j) (fun i => hψ i j)).some

theorem jhMult_leviChar_cellFunctor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  intro k _ _ _ _ hC α β _ _ _ _ m _ _ c _ _ f g X _ _ ρ hρ hl χ hχ
  obtain ⟨T, hT0, hT⟩ := hC α β m (fun _ => Unit) c f g X ρ hρ hl
  have h1 := hT (IrrRep.ofChar (leviChar (fun _ : β => Unit) χ) (isSmoothChar_leviChar_of_smooth _ hχ))
  refine Eq.trans h1 ?_
  let s₀ : ∀ i j, IrrCl (GL (c i j) k) := fun i j => (IrrRep.det (c i j) (χ j) (hχ j)).cl
  have e₀ : ∀ i j, Nonempty ((s₀ i j).rep.ρ.Equiv (detRep (c i j) (χ j))) := fun i j =>
    (IrrRep.det (c i j) (χ j) (hχ j)).nonempty_equiv_rep
  have hfac : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ) (jac (f i) (ρ i)) =
      jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := fun i =>
    jhMult_congr_left ((LocGL.piTensorEquiv fun j => (e₀ i j).some).trans
      (nonempty_piTensor_detRep_equiv k β (c i) χ).some) _
  rw [Finset.sum_eq_single s₀]
  · obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s₀ i j).rep) (fun _ j => χ j)
      (fun _ j => hχ j) e₀
    have h2 : jhMult (ofChar (leviChar (fun _ : β => Unit) χ))
        (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) = 1 :=
      (jhMult_congr_right _ a).trans (jhMult_self (isIrreducible_ofChar _))
    exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => hfac i) h2).trans (mul_one _)
  · intro s _ hs
    have hsub : ∀ i j, Subsingleton (c i j) := fun i j =>
      ⟨fun x y => sigma_mk_injective (β := fun i => c i j) ((g j).injective (Subsingleton.elim _ _))⟩
    choose ψ hψ e using fun i j =>
      GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one k (c i j) _ (s i j).rep.ρ (s i j).rep.smooth (s i j).rep.irr
    obtain ⟨a⟩ := nonempty_cell_term_equiv g (fun i j => (s i j).rep) ψ hψ e
    refine mul_eq_zero_of_right _ ((jhMult_congr_right _ a).trans (Model.jhMult_ofChar_ne fun h => hs ?_))
    have h3 := leviChar_unit_injective h
    funext i j
    have h4 : detChar (c i j) (ψ i j) = detChar (c i j) (χ j) := by
      rcases isEmpty_or_nonempty (c i j) with hc | ⟨⟨x⟩⟩
      · ext1 y
        rw [detChar_apply, detChar_apply, show Matrix.GeneralLinearGroup.det y = 1 from
          Units.ext (by simp), map_one, map_one]
      · have : (g j).symm () = ⟨i, x⟩ := (g j).injective (Subsingleton.elim _ _)
        rw [congrFun h3 j, this]
    rw [← (s i j).cl_rep]
    refine IrrRep.cl_eq_iff.2 ⟨(e i j).some.trans ?_⟩
    show (ofChar (detChar (c i j) (ψ i j))).Equiv (ofChar (detChar (c i j) (χ j)))
    rw [h4]
    exact .refl _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.SmGL.Exponents
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityLeviCharGeometricLemmaCeStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_leviChar_geometricLemmaCell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  first | exact @GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor | exact GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor | (intros; apply GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor <;> assumption)
end
end
