module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtAlgCompRight
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEqStatement

section

@[expose] public section

theorem GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq :
    type_of% (@GlobalTheory.PtExt.bcPull_sumMul_fv) :=
  @GlobalTheory.PtExt.bcPull_sumMul_fv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointwiseCoboundaryOfPullbackBaseChangeIsIso

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

namespace BcIso

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

def ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : R' →+* E :=
  (Spec.preimage (R := CommRingCat.of R') (S := CommRingCat.of E) (g ≫ X'.hom)).hom

theorem spMap_ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : spMap (ringOf g) = g ≫ X'.hom := by
  unfold ringOf
  exact Spec.map_preimage _

theorem ringOf_eq_of_spMap {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) (τ : R' →+* E)
    (h : spMap τ = g ≫ X'.hom) : ringOf g = τ := by
  have h1 : spMap (ringOf g) = spMap τ := by rw [spMap_ringOf, h]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

def ptBack [IsIso q] {E : Type} [CommRing E] (g : Sp E ⟶ X.left) :
    @Pt R' _ X' E _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra := by
  letI : Algebra R' E := (ringOf (X' := X') (g ≫ inv q)).toAlgebra
  exact Over.homMk (U := SpAlg R' E) (V := X') (g ≫ inv q)
    (spMap_ringOf (X' := X') (g ≫ inv q)).symm

theorem ringOf_comp (w : q ≫ X.hom = X'.hom ≫ spMap σ) [IsIso q] {E : Type} [CommRing E] [Algebra R E]
    (z : Pt X E) : (ringOf (X' := X') (z.left ≫ inv q)).comp σ = algebraMap R E := by
  have h1 : spMap ((ringOf (X' := X') (z.left ≫ inv q)).comp σ) = spMap (algebraMap R E) := by
    rw [spMap_comp, spMap_ringOf]
    simp only [Category.assoc, ← w, IsIso.inv_hom_id_assoc]
    exact Over.w z
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem bcPull_transport (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) (E E' : Type) [CommRing E] [CommRing E']
    (A : Algebra R' E) (A' : Algebra R' E') (i : Algebra R E) (i' : Algebra R E') (h : i = algVia σ E)
    (h' : i' = algVia σ E') (φ : @AlgHom R E E' _ _ _ i i') (z : @Pt R _ X E _ i) (ψ : E →ₐ[R'] E')
    (y : Pt X' E) (hψ : ∀ e, ψ e = φ e) (hy : y.left ≫ q = z.left) :
    @u E _ i E' _ i' φ z = bcPull w u E E' ψ y := by
  subst h h'
  letI := algVia σ E
  letI := algVia σ E'
  have e1 : homVia σ ψ = φ := AlgHom.ext hψ
  have e2 : ptVia w y = z := by
    apply Over.OverMorphism.ext
    exact hy
  rw [← e1, ← e2]
  rfl

end BcIso

open BcIso

theorem isCob_of_bcPull_isIso : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R))
    (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ), IsIso q → ∀ u : Fn1 X,
    IsCoc (whole X) u → (∃ k, IsCob (whole X') (bcPull w u) k) → ∃ k, IsCob (whole X) u k := by
  intro R R' _ _ σ X X' q w hq u _ hk
  obtain ⟨k', hk'⟩ := hk
  refine ⟨fun E _ _ z ↦ @k' E _ (ringOf (X' := X') (z.left ≫ inv q)).toAlgebra (ptBack z.left), ?_⟩
  intro E _ i E' _ i' φ z _
  let τ := ringOf (X' := X') (z.left ≫ inv q)
  let τ' := ringOf (X' := X') ((spOver φ ≫ z).left ≫ inv q)
  letI A : Algebra R' E := τ.toAlgebra
  letI A' : Algebra R' E' := τ'.toAlgebra
  have hτ : τ' = (φ : E →+* E').comp τ := by
    apply ringOf_eq_of_spMap
    rw [spMap_comp, spMap_ringOf]
    simp only [Over.comp_left, Category.assoc]
    rfl
  have hc : ∀ r, φ (τ r) = τ' r := fun r ↦ by rw [hτ]; rfl
  let ψ : E →ₐ[R'] E' := { (φ : E →+* E') with commutes' := hc }
  have h : i = algVia σ E := Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w z)).symm
  have h' : i' = algVia σ E' :=
    Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w (spOver φ ≫ z))).symm
  have e1 := bcPull_transport w u E E' A A' i i' h h' φ z ψ (ptBack z.left) (fun _ ↦ rfl)
    (by simp [ptBack])
  have e2 := hk' E E' ψ (ptBack z.left) (sm_whole _)
  have e3 : spOver ψ ≫ ptBack (X' := X') z.left = ptBack (spOver φ ≫ z).left :=
    Over.OverMorphism.ext (by simp [ptBack]; rfl)
  rw [e1, e2, e3]
  rfl

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointwiseCoboundaryOfPullbackBaseChangeIsIsoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPointwiseCoboundary_of_pullbackBaseChange_isIso : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ), IsIso q → ∀ u : Fn1 X, IsCoc (whole X) u → (∃ k, IsCob (whole X') (bcPull w u) k) → ∃ k, IsCob (whole X) u k := by
  first | exact @GlobalTheory.PtExt.isCob_of_bcPull_isIso | exact GlobalTheory.PtExt.isCob_of_bcPull_isIso | (intros; apply GlobalTheory.PtExt.isCob_of_bcPull_isIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryWStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  first | exact @GlobalTheory.PtExt.bcPull_keeps | exact GlobalTheory.PtExt.bcPull_keeps | (intros; apply GlobalTheory.PtExt.bcPull_keeps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SurjD

theorem exists_fin_sum_tmul {R D M : Type*} [CommRing R] [CommRing D] [Algebra R D] [AddCommGroup M]
    [Module R M] (z : D ⊗[R] M) : ∃ (n : ℕ) (d : Fin n → D) (m : Fin n → M), z = ∑ i, d i ⊗ₜ m i := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  refine ⟨S.card, fun i ↦ (S.equivFin.symm i).1.1, fun i ↦ (S.equivFin.symm i).1.2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp S.equivFin.symm (fun p : S ↦ p.1.1 ⊗ₜ p.1.2)).symm

theorem cohom_of_cob {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {u a b c : Fn1 X} (h : Cohom W u a) (k : Fn0 X) (hk : IsCob W c k)
    (ha : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D), a D D' φ x = c D D' φ x + b D D' φ x) : Cohom W u b := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨fun D _ _ x ↦ k₀ D x + k D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have h1 := hk₀ D D' φ x hx
  have h2 := hk D D' φ x hx
  have h3 := ha D D' φ x
  simp only [Fn1.add, Fn1.neg, map_add] at h1 ⊢
  linear_combination h1 + h2 + h3

end GlobalTheory.PtExt.SurjD


open GlobalTheory.PtExt.SurjD in
theorem GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  intro H R _ B _ g hB hg D _ _ u hu
  obtain ⟨B', _, π, q, hpb, hB', hg', hq, hfst, hsnd⟩ :=
    GlobalTheory.exists_baseChange_spAlg_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (fst (SpAlg R D) B), ← Category.assoc, hfst]
    rfl
  have hu' := (GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole R D (algebraMap R D) _ B' q w u).1 hu
  have hsurj := GlobalTheory.PtExt.toH1O_surjective_of_abelian H D B' g hB' hg'
  obtain ⟨f', hf'⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective D B' hsurj (bcPull w u) hu'
  obtain ⟨hFree, -, hBC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  have hbc := (hBC R B g hB hg D B' π hpb).1
  have hall : prim (dp0 D) (𝟙 _) B' = ⊤ := (hFree D B' g hB' hg').1
  have hmem : H1.mk _ f' ∈ prim (dp0 D) (𝟙 _) B' := by rw [hall]; exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hbc.2 ⟨H1.mk _ f', hmem⟩
  obtain ⟨n, d, m, rfl⟩ := exists_fin_sum_tmul z
  choose β hβ using fun i ↦ H1.mk_surjective _ (m i).1
  refine ⟨n, d, β, ?_⟩
  let mB := (GlobalTheory.Published.AbelianDeRham.bcMor hpb).isMor
  let S : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _)) := ∑ i, d i • mB.coef.pullbackOneCocycle (β i)
  have hcl : H1.mk _ f' = H1.mk _ S := by
    have e := congrArg Subtype.val hz

    simp only [map_sum, liftSemi_tmul] at e
    rw [← e]

    simp only [S, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, GrpMor.coe_pull]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hβ i]
    rfl
  obtain ⟨g₀, hg₀⟩ := H1.mk_eq_mk.1 hcl
  obtain ⟨hadd, -, hcob⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  obtain ⟨k, hk⟩ := hcob g₀
  have hsplit : f' = ⟨d0 _ g₀, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g₀⟩ + S := Subtype.ext (by simp [hg₀])
  have hC : Cohom (whole B') (bcPull w u) (fv S) := by
    refine cohom_of_cob hf' k hk ?_
    rw [hsplit, hadd]
    intros
    rfl
  have hsum := GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq R D B B' q w π hfst hsnd mB (Fin n) d β
  obtain ⟨k', hk'⟩ : ∃ k, IsCob (whole B') (bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg)) k := by
    obtain ⟨k', hk'⟩ := hC
    refine ⟨k', ?_⟩
    have e : bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg) = (bcPull w u).add (fv S).neg := by
      rw [← hsum]; rfl
    rw [e]; exact hk'
  have hsm : IsCoc (whole _) (sumMul d fun i ↦ fv (β i)) :=
    (GlobalTheory.PtExt.SumMulFacts.main R D B (Fin n) d _).1 fun i ↦ (fv_isCoc_and_ev_eq R B (β i)).1
  have hdiff : IsCoc (whole _) (u.add (sumMul d fun i ↦ fv (β i)).neg) := by
    intro E _ _ E' _ _ E'' _ _ φ ψ x hx
    have h1 := hu E E' E'' φ ψ x hx
    have h2 := hsm E E' E'' φ ψ x hx
    simp only [Fn1.add, Fn1.neg, map_add (f := _), map_neg]
    linear_combination h1 - h2
  exact GlobalTheory.T.isPointwiseCoboundary_of_pullbackBaseChange_isIso R D (algebraMap R D) _ B' q w hq _ hdiff ⟨k', hk'⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMulStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  first | exact @GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | exact GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | (intros; apply GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian <;> assumption)
end
end
