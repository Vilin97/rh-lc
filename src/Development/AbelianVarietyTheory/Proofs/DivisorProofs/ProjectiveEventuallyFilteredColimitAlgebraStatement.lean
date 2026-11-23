module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimitStatement
public import Mathlib.LinearAlgebra.TensorProduct.Defs
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
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.MvPolynomial.Eval
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplitStatement
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChange

section

@[expose] public section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_presentation_matrix : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  intro R B M _ _ _ _ _ n m π hπ r hr hP
  let e := TensorProduct.piScalarRight R B B (Fin n)
  let πB : (Fin n → B) →ₗ[B] B ⊗[R] M := (π.baseChange B) ∘ₗ e.symm.toLinearMap
  have hπB : Function.Surjective πB := (LinearMap.lTensor_surjective B hπ).comp e.symm.surjective
  obtain ⟨i, hi⟩ := Module.projective_lifting_property πB LinearMap.id hπB
  let v : Fin n → Fin n → B := fun a => i ((1 : B) ⊗ₜ[R] π (Pi.single a 1))
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R r
  have hex : Function.Exact f π := by
    rw [LinearMap.exact_iff, Fintype.range_linearCombination, hr]
  have hexB := lTensor_exact B hex hπ
  let N : Submodule B (Fin n → B) := Submodule.span B (Set.range fun b l => algebraMap R B (r b l))
  have hker : ∀ y, πB y = 0 → y ∈ N := by
    intro y hy
    have h0 : (π.lTensor B) (e.symm y) = 0 := by
      have := hy
      simp only [πB, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
      rwa [LinearMap.baseChange_eq_ltensor] at this
    obtain ⟨z, hz⟩ := (hexB _).1 h0
    have hy' : y = e (f.lTensor B z) := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [hy']
    clear hz hy' h0 hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        have : e ((f.lTensor B) (x ⊗ₜ c)) = ∑ b, (x * algebraMap R B (c b)) • (fun l => algebraMap R B (r b l)) := by
          ext l
          simp [e, f, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def, Finset.mul_sum,
            Finset.sum_mul, mul_comm, mul_left_comm]
        rw [this]
        exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem ha hb
  have hπv : ∀ a, πB (v a - Pi.single a 1) = 0 := by
    intro a
    have h1 : πB (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := LinearMap.congr_fun hi _
    have h2 : e.symm (Pi.single a 1) = (1 : B) ⊗ₜ[R] (Pi.single a 1 : Fin n → R) := by
      rw [LinearEquiv.symm_apply_eq]
      ext l
      simp [e, Pi.single_apply]
    rw [map_sub, h1]
    simp [πB, h2]
  choose w hw using fun a => (Submodule.mem_span_range_iff_exists_fun B).1 (hker _ (hπv a))
  refine ⟨v, w, fun b l => ?_, fun a l => ?_⟩
  · have hrb : π (r b) = 0 := by
      have : r b ∈ LinearMap.ker π := hr ▸ Submodule.subset_span ⟨b, rfl⟩
      exact this
    have hsum : (1 : B) ⊗ₜ[R] π (r b) = ∑ a, algebraMap R B (r b a) • ((1 : B) ⊗ₜ[R] π (Pi.single a 1)) := by
      conv_lhs => rw [← Finset.univ_sum_single (r b)]

      simp only [map_sum, TensorProduct.tmul_sum, algebraMap_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← TensorProduct.tmul_smul, ← map_smul]
      congr 2
      ext j
      simp [Pi.single_apply]
    have h1 : ∑ a, algebraMap R B (r b a) • v a = 0 := by

      simp only [v, ← map_smul, ← map_sum, ← hsum, hrb, TensorProduct.tmul_zero, map_zero]
    have := congrFun h1 l
    simpa [Finset.sum_apply, Algebra.smul_def] using this
  · have := congrFun (hw a) l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply] at this
    rw [this]
    simp [eq_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChangeStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimit

section

@[expose] public section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem poly_eventually_solvable :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  classical
  intro J _ _ F c hc j σ ι _ _ p x hx
  haveI := Fintype.ofFinite σ
  haveI := Fintype.ofFinite ι
  have hc' := isColimitOfPreserves (forget _) hc

  choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self j _)
  have hm : ∀ s, Nonempty (jx s ⟶ K) := fun s =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))
  let u : σ → F.obj K := fun s => (F.map (hm s).some).hom (x' s)
  have hu : ∀ s, (c.ι.app K).hom (u s) = x s := by
    intro s
    have h2 := congr(($(c.w (hm s).some)).hom (x' s))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact hx' s

  have hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = x := funext hu
    rw [e1, e2]; exact hx i

  have one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    have h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0 := by
      rw [hz i, map_zero]
    obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)
    refine ⟨k₀, f₀, fun k f => ?_⟩
    have e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by simpa using e
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

  have all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a S _ ih =>
      obtain ⟨k₀, f₀, hh⟩ := eventually_and
        (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0)
        (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0)
        (one a) ih
      refine ⟨k₀, f₀, fun k f i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hh k f).1
      · exact (hh k f).2 i hi
  obtain ⟨k₀, f₀, h0⟩ := all Finset.univ
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩
  have := h0 k f i (Finset.mem_univ i)
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

end GlobalTheory.TorsorColim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimitStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.polynomial_system_eventually_solvable_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  first | (exact @GlobalTheory.TorsorColim.poly_eventually_solvable) | (exact GlobalTheory.TorsorColim.poly_eventually_solvable) | (intros; apply GlobalTheory.TorsorColim.poly_eventually_solvable  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebra

section

@[expose] public section

open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.ProjColim

noncomputable def sysPoly {R : Type} [CommRing R] (n m : ℕ) (r : Fin m → Fin n → R) :
    (Fin m × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin m)) R
  | .inl (b, l) => ∑ a, MvPolynomial.C (r b a) * MvPolynomial.X (.inl (a, l))
  | .inr (a, l) => MvPolynomial.X (.inl (a, l)) - (if a = l then 1 else 0) -
      ∑ b, MvPolynomial.X (.inr (a, b)) * MvPolynomial.C (r b l)

theorem eval₂_sysPoly_eq_zero_iff {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (n m : ℕ)
    (r : Fin m → Fin n → R) (x : (Fin n × Fin n) ⊕ (Fin n × Fin m) → B) :
    (∀ i, MvPolynomial.eval₂ φ x (sysPoly n m r i) = 0) ↔
      (∀ b l, ∑ a, φ (r b a) * x (.inl (a, l)) = 0) ∧
      (∀ a l, x (.inl (a, l)) = (if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
  have key : ∀ a l, MvPolynomial.eval₂ φ x (sysPoly n m r (.inr (a, l))) =
      x (.inl (a, l)) - ((if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
    intro a l
    by_cases h : a = l <;> simp [sysPoly, MvPolynomial.eval₂_sum, h, sub_sub]
  constructor
  · intro h
    refine ⟨fun b l => ?_, fun a l => ?_⟩
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h (.inl (b, l))
    · have := h (.inr (a, l))
      rw [key] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2⟩ (⟨b, l⟩ | ⟨a, l⟩)
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h1 b l
    · rw [key, sub_eq_zero]
      exact h2 a l

theorem projective_eventually_of_finitePresentation : ∀ (J : Type) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{0}) (c : Cocone F), IsColimit c → ∀ (j : J) (M : Type) [AddCommGroup M]
    [Module (F.obj j) M] [Module.FinitePresentation (F.obj j) M],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Projective c.pt (c.pt ⊗[F.obj j] M)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] M) := by
  intro J _ _ F c hc j M _ _ _ hproj
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (F.obj j) M
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let π : (Fin n → F.obj j) →ₗ[F.obj j] M := e.symm.toLinearMap ∘ₗ K.mkQ
  have hπ : Function.Surjective π := e.symm.surjective.comp K.mkQ_surjective
  have hker : Submodule.span (F.obj j) (Set.range r) = LinearMap.ker π := by
    rw [hr, LinearMap.ker_comp, LinearEquiv.ker]
    exact (Submodule.ker_mkQ K).symm
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨v, w, h1, h2⟩ := GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange (F.obj j) c.pt M n m π hπ r hker hproj
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.polynomial_system_eventually_solvable_colimit J F c hc j _ _ (sysPoly n m r)
    (Sum.elim (fun p => v p.1 p.2) (fun p => w p.1 p.2))
    ((eval₂_sysPoly_eq_zero_iff _ n m r _).mpr ⟨h1, h2⟩)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨y, hy⟩ := hk k f
  obtain ⟨h1', h2'⟩ := (eval₂_sysPoly_eq_zero_iff _ n m r y).mp hy
  exact GlobalTheory.T.projective_baseChange_of_presentation_matrix_split (F.obj j) (F.obj k) M n m π hπ r hker (fun a l => y (.inl (a, l)))
    (fun a b => y (.inr (a, b))) h1' h2'

theorem projective_eventually : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  intro J _ _ F c hc j A _ _ _ hfp
  obtain ⟨hfin, hproj⟩ := hfp
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨k₁, g₁, hk₁⟩ := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc j A hfin
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map (g₁ ≫ 𝟙 k₁)).hom.toAlgebra
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hk₁ k₁ (𝟙 k₁)
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [← c.w (g₁ ≫ 𝟙 k₁)]; rfl)
  haveI : Module.Projective c.pt (c.pt ⊗[F.obj j] A) := hproj
  have hproj₁ : Module.Projective c.pt (c.pt ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) :=
    Module.Projective.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) c.pt c.pt A).symm
  obtain ⟨k₀, g₀, hk₀⟩ :=
    projective_eventually_of_finitePresentation J F c hc k₁ (F.obj k₁ ⊗[F.obj j] A) hproj₁
  refine ⟨k₀, (g₁ ≫ 𝟙 k₁) ≫ g₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (g₀ ≫ f)).hom.toAlgebra
  haveI : Module.Projective (F.obj k) (F.obj k ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) := hk₀ k f
  letI : Algebra (F.obj j) (F.obj k) := (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom x = (F.map (g₀ ≫ f)).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [Category.assoc, F.map_comp (g₁ ≫ 𝟙 k₁)]; rfl)
  exact Module.Projective.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) (F.obj k) (F.obj k) A)

end GlobalTheory.ProjColim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebraStatement

section

@[expose] public section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.projective_eventually_filteredColimit_algebra : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  first | (exact @GlobalTheory.ProjColim.projective_eventually) | (exact GlobalTheory.ProjColim.projective_eventually) | (intros; apply GlobalTheory.ProjColim.projective_eventually  <;> assumption)
end
end
