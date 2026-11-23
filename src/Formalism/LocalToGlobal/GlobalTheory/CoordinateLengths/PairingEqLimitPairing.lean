module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.LocalBasisChangeDecompCompatible
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL6.LinearIndependentProdRenameOfCard

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

variable {K : Type*} [Field K] {S₁ S₂ : Type*}

theorem sumAlgEquiv_rename_inl (a : MvPolynomial S₁ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inl a) = map (C : K →+* MvPolynomial S₂ K) a := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K S₁ S₂) a
  simpa [MvPolynomial.algebraMap_eq] using h

theorem sumAlgEquiv_rename_inr_eq_C' (b : MvPolynomial S₂ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inr b) = C b := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K S₁ S₂) b
  simpa [MvPolynomial.algebraMap_eq] using h

def mvPolynomialCoeffInFirstVariables (m : S₁ →₀ ℕ) : MvPolynomial (S₁ ⊕ S₂) K →ₗ[K] MvPolynomial S₂ K :=
  (lcoeff (MvPolynomial S₂ K) m).restrictScalars K ∘ₗ (sumAlgEquiv K S₁ S₂).toLinearMap

theorem leftCoeff_rename_mul (m : S₁ →₀ ℕ) (a : MvPolynomial S₁ K) (b : MvPolynomial S₂ K) :
    mvPolynomialCoeffInFirstVariables m (rename Sum.inl a * rename Sum.inr b) = AddMonoidAlgebra.coeff a m • b := by
  simp only [mvPolynomialCoeffInFirstVariables, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.restrictScalars_apply,
    lcoeff_apply, map_mul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C']
  rw [mul_comm, coeff_C_mul, coeff_map, smul_eq_C_mul, mul_comm]

theorem linearIndependent_rename_mul {κ₁ κ₂ : Type*} (v : κ₁ → MvPolynomial S₁ K) (w : κ₂ → MvPolynomial S₂ K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K fun p : κ₁ × κ₂ => rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
  have h := (hw.tmul_of_isDomain hv).comp Prod.swap Prod.swap_injective
  let e : TensorProduct K (MvPolynomial S₂ K) (MvPolynomial S₁ K) ≃ₗ[K] MvPolynomial (S₁ ⊕ S₂) K :=
    ((algebraTensorAlgEquiv K (MvPolynomial S₂ K) (σ := S₁)).restrictScalars K).toLinearEquiv.trans
      (sumAlgEquiv K S₁ S₂).symm.toLinearEquiv
  have he : ∀ p : κ₁ × κ₂, e (TensorProduct.tmul K (w p.2) (v p.1)) =
      rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
    intro p
    apply (sumAlgEquiv K S₁ S₂).injective
    simp [e, algebraTensorAlgEquiv_tmul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C', smul_eq_C_mul, MvPolynomial.algebraMap_eq,
      mul_comm]
  have h2 := h.map' e.toLinearMap e.ker
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, LinearEquiv.coe_coe, he] using h2

def sumComplementToProduct {ι σ : Type} (i : ι) : σ ⊕ ({j // j ≠ i} × σ) → ι × σ :=
  Sum.elim (fun x => (i, x)) (fun p => (p.1.1, p.2))

theorem splitIndex_injective {ι σ : Type} (i : ι) : Function.Injective (sumComplementToProduct (σ := σ) i) := by
  intro x y h
  rcases x with x | ⟨⟨j, hj⟩, x⟩ <;> rcases y with y | ⟨⟨j', hj'⟩, y⟩ <;>
    simp only [sumComplementToProduct, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
  all_goals first
    | exact absurd h.1.symm hj'
    | exact absurd h.1 hj
    | simp_all

theorem linearIndependent_prod_rename_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {σ : Type} (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K), (∀ τ, LinearIndependent K (b τ)) →
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  induction n with
  | zero =>
    intro ι _ _ hι σ κ b hb
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    haveI : Unique (∀ τ, κ τ) := Pi.uniqueOfIsEmpty κ
    rw [linearIndependent_unique_iff]
    simp
  | succ n ih =>
    intro ι _ _ hι σ κ b hb
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hcard : Fintype.card {τ // τ ≠ τ₀} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι]; omega
    have hW := ih {τ // τ ≠ τ₀} hcard (fun τ => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1)
    have hP := linearIndependent_rename_mul (b τ₀) _ (hb τ₀) hW
    have hR := hP.map' (rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap
      (LinearMap.ker_eq_bot.2 (rename_injective _ (splitIndex_injective τ₀)))
    have h2 := hR.comp (Equiv.piSplitAt τ₀ κ) (Equiv.piSplitAt τ₀ κ).injective
    have key : ∀ g : (∀ τ, κ τ), ∏ τ, rename (Prod.mk τ) (b τ (g τ)) =
        rename (sumComplementToProduct (σ := σ) τ₀) (rename Sum.inl (b τ₀ (g τ₀)) *
          rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ.1)))) := by
      intro g
      simp only [map_mul, map_prod, rename_rename]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ τ₀]
      rfl
    have hfun : (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) =
        ((rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap ∘ (fun p : κ τ₀ × (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
          rename Sum.inl (b τ₀ p.1) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (p.2 τ))))) ∘
          (Equiv.piSplitAt τ₀ κ) := by
      funext g
      rw [key g]
      rfl
    rw [hfun]
    exact h2

theorem linearIndependent_prod_rename_of_forall {ι σ : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K)
    (hb : ∀ τ, LinearIndependent K (b τ)) :
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  exact linearIndependent_prod_rename_of_card _ ι rfl κ b hb

section Len

theorem length_quot_map_of_injective {O M M' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (hf : Function.Injective f) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := by
  have h : (B.comap A.subtype).map (Submodule.equivMapOfInjective f hf A : A →ₗ[O] A.map f) =
      (B.map f).comap (A.map f).subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hxA⟩, hxB, hx⟩
      refine ⟨x, hxB, ?_⟩
      have hx' := congrArg Subtype.val hx
      exact hx'
    · rintro ⟨x, hxB, rfl⟩
      obtain ⟨x', hx'A, hx'⟩ := Submodule.mem_map.1 hy
      have hxx : x' = x := hf hx'
      subst hxx
      exact ⟨⟨x', hx'A⟩, hxB, Subtype.ext rfl⟩
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A) h).length_eq.symm

theorem length_quot_pi_const {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (G : Type*) [Fintype G] [DecidableEq G]
    (A B : Submodule O M) :
    Module.length O ((Submodule.pi Set.univ fun _ : G => A) ⧸
        (Submodule.pi Set.univ fun _ : G => B).comap (Submodule.pi Set.univ fun _ : G => A).subtype) =
      Fintype.card G • Module.length O (A ⧸ B.comap A.subtype) := by
  set P := Submodule.pi Set.univ fun _ : G => A with hP
  set B' := B.comap A.subtype with hB'
  let pr : G → P →ₗ[O] A := fun g =>
    LinearMap.codRestrict A ((LinearMap.proj g).comp P.subtype) (fun x => x.2 g (Set.mem_univ g))
  let φ : P →ₗ[O] (G → A ⧸ B') := LinearMap.pi fun g => B'.mkQ.comp (pr g)
  have hsurj : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective B' (y g)
    refine ⟨⟨fun g => (x g : M), fun g _ => (x g).2⟩, ?_⟩
    funext g
    simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ fun _ : G => B).comap P.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h g
      have hg := congrFun h g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap] at hg
      exact hg
    · intro h
      funext g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap]
      exact h g
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective φ hsurj)
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]

end Len

section Psi

variable {K : Type*} [Field K]

theorem eq_zero_of_sum_rename_mul {S₁ S₂ κ : Type*} [Fintype κ] (w : κ → MvPolynomial S₂ K) (hw : LinearIndependent K w)
    (a : κ → MvPolynomial S₁ K) (h : ∑ j, rename Sum.inl (a j) * rename Sum.inr (w j) = 0) : a = 0 := by
  funext j
  ext m
  have h' := congrArg (mvPolynomialCoeffInFirstVariables (K := K) (S₁ := S₁) (S₂ := S₂) m) h

  simp only [map_sum, leftCoeff_rename_mul, map_zero] at h'
  simpa using (Fintype.linearIndependent_iff.1 hw) (fun j => AddMonoidAlgebra.coeff (a j) m) h' j

def mvPolynomialProductExtension {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) :
    ((∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial σ K) →ₗ[K] MvPolynomial (ι × σ) K where
  toFun h := ∑ g, rename (Prod.mk τ₀) (h g) * ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ.1) (b τ.1 (g τ))
  map_add' h h' := by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  map_smul' c h := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

theorem factorMap_injective {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ)) :
    Function.Injective (mvPolynomialProductExtension τ₀ κ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hW : LinearIndependent K (fun g : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
      ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) :=
    linearIndependent_prod_rename_of_forall (fun τ : {τ // τ ≠ τ₀} => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1 τ.2)
  have key : mvPolynomialProductExtension τ₀ κ b h = rename (sumComplementToProduct (σ := σ) τ₀) (∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))) := by

    simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, rename_rename]
    rfl
  rw [key] at hh
  have hh' : ∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) = 0 :=
    rename_injective _ (splitIndex_injective τ₀) (by rw [hh, map_zero])
  exact eq_zero_of_sum_rename_mul _ hW h hh'

theorem length_quot_map_positionMap {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ))
    (O : Subring K) (A₀ B₀ : Submodule O (MvPolynomial σ K)) :
    Module.length O (((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
          ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)) ⧸
        ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => B₀).map ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).comap
          ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
            ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) • Module.length O (A₀ ⧸ B₀.comap A₀.subtype) := by
  rw [length_quot_map_of_injective _ (show Function.Injective ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) from
    factorMap_injective τ₀ κ b hb), length_quot_pi_const, Fintype.card_pi]

end Psi

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingEqLimitPairing

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Cls

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
  [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial (Fin N × Fin N) ℂ) (O : Subring ℂ)

def tenSpan : Submodule O (MvPolynomial (ι × Fin N × Fin N) ℂ) :=
  Submodule.span O (Set.range fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ => b τ (g τ)))

def gRest (g : ∀ τ, κ τ) : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1 := fun τ => g τ.1

def gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : ∀ τ, κ τ :=
  fun τ => if h : τ = τ₀ then (by subst h; exact k) else g ⟨τ, h⟩

theorem gRest_gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gRest τ₀ κ (gExt τ₀ κ g k) = g := by
  funext τ
  unfold gRest gExt
  rw [dite_eq_right τ.2]

theorem gExt_self (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gExt τ₀ κ g k τ₀ = k := by
  unfold gExt
  rw [dite_eq_left rfl]

theorem ten_eq_psi (g : ∀ τ, κ τ) :
    Formalism.L2.Forms.ten (fun τ => b τ (g τ)) = mvPolynomialProductExtension τ₀ κ b (Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀))) := by
  classical
  unfold Formalism.L2.Forms.ten
  simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (gRest τ₀ κ g)]
  · rw [Pi.single_eq_same]
    exact Fintype.prod_eq_mul_prod_subtype_ne _ τ₀
  · intro g' _ hg'
    rw [Pi.single_eq_of_ne hg', map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tenSpan_eq_psi (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) :
    tenSpan κ b O = (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
      ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  apply le_antisymm
  · rw [tenSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [ten_eq_psi τ₀ κ b g]
    refine ⟨Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀)), ?_, rfl⟩
    intro g' _
    by_cases hg : g' = gRest τ₀ κ g
    · subst hg
      rw [Pi.single_eq_same, hΛ]
      exact Submodule.subset_span ⟨g τ₀, rfl⟩
    · rw [Pi.single_eq_of_ne hg]
      exact Λ.zero_mem
  · rintro _ ⟨h, hh, rfl⟩
    have hsingle : ∀ (g' : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (v : MvPolynomial (Fin N × Fin N) ℂ), v ∈ Λ →
        mvPolynomialProductExtension τ₀ κ b (Pi.single g' v) ∈ tenSpan κ b O := by
      intro g' v hv
      have hle : Λ ≤ (tenSpan κ b O).comap (((mvPolynomialProductExtension τ₀ κ b).restrictScalars O).comp
          (LinearMap.single O (fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => MvPolynomial (Fin N × Fin N) ℂ) g')) := by
        rw [hΛ, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have h1 := ten_eq_psi τ₀ κ b (gExt τ₀ κ g' k)
        rw [gRest_gExt, gExt_self] at h1
        show mvPolynomialProductExtension τ₀ κ b (Pi.single g' (b τ₀ k)) ∈ tenSpan κ b O
        rw [← h1]
        exact Submodule.subset_span ⟨gExt τ₀ κ g' k, rfl⟩
      exact hle hv
    have hsum : h = ∑ g', Pi.single g' (h g') := (Finset.univ_sum_single h).symm
    show mvPolynomialProductExtension τ₀ κ b h ∈ tenSpan κ b O

    rw [hsum, map_sum]
    exact Submodule.sum_mem _ fun g' _ => hsingle g' (h g') (hh g' (Set.mem_univ _))

theorem psi_subP (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (h : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Forms.subP o (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ₀) (h g)) := by
  have hren : ∀ (τ : ι) (q : MvPolynomial (Fin N × Fin N) ℂ),
      Formalism.L2.Forms.subP o (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) q) := by
    intro τ q
    have h1 : (Formalism.L2.Forms.subP o).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ)) := by
      apply MvPolynomial.algHom_ext
      intro v

      simp [Formalism.L2.Forms.subP, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
    exact AlgHom.congr_fun h1 q
  have hone : ∀ q : MvPolynomial (Fin N × Fin N) ℂ, Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) q = q := by
    intro q
    have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (1 : Matrix (Fin N) (Fin N) ℂ) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    rw [h1, AlgHom.id_apply]

  simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, hren]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [ho τ.1 τ.2, hone]

theorem map_psi_pi (L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (Fin N × Fin N) ℂ)
    (L' : MvPolynomial (ι × Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (hc : ∀ h, L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => L (h g)))
    (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)) :
    ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map L' =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map L).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨fun g => L (h g), fun g _ => ⟨h g, hh g (Set.mem_univ _), rfl⟩, ?_⟩
    exact (hc h).symm
  · rintro ⟨h', hh', rfl⟩
    have hh'' : ∀ g, ∃ y ∈ Λ, L y = h' g := fun g => hh' g (Set.mem_univ _)
    choose h hh hhe using hh''
    refine ⟨mvPolynomialProductExtension τ₀ κ b h, ⟨h, fun g _ => hh g, rfl⟩, ?_⟩
    show L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b h'
    rw [hc]
    congr 1
    funext g
    exact hhe g

abbrev scO (σ : Type) (c : ℂ) : MvPolynomial σ ℂ →ₗ[O] MvPolynomial σ ℂ :=
  (c • LinearMap.id : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ).restrictScalars O

theorem cls_len (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent ℂ (b τ)) (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (c₁ c₂ : ℂ) :
    Module.length O
      ((((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)) ⧸
        ((tenSpan κ b O).map (scO O _ c₂)).comap
          (((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) •
        Module.length O (((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)) ⧸
          (Λ.map (mvPolynomialScalingMap O c₂)).comap ((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)).subtype) := by
  have hrow : (tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    rw [tenSpan_eq_psi τ₀ κ b O Λ hΛ]
    exact map_psi_pi τ₀ κ b O (mvPolynomialRowLinearMap O (o τ₀)) ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)
      (fun h => psi_subP τ₀ κ b o ho h) Λ
  have hsc : ∀ (c : ℂ) (Λ' : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)),
      ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ').map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map (scO O _ c) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ'.map (mvPolynomialScalingMap O c)).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    intro c Λ'
    refine map_psi_pi τ₀ κ b O (mvPolynomialScalingMap O c) (scO O _ c) (fun h => ?_) Λ'
    show c • mvPolynomialProductExtension τ₀ κ b h = mvPolynomialProductExtension τ₀ κ b (fun g => c • h g)
    rw [← map_smul]
    rfl
  rw [hrow, hsc, tenSpan_eq_psi τ₀ κ b O Λ hΛ, hsc]
  exact length_quot_map_positionMap τ₀ κ b hb O _ _

end Cls

end Formalism.L2.GlobalTheoryTheory.LemB
end
end
end
