module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelianStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticomm

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem cup_anticomm (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : GlobalTheory.CatCoh.H1 F) : cup F a b = - cup F b a := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp a, Z1.comp b, map_mul, map_neg]
  ring

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticommStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (a b : GlobalTheory.CatCoh.H1 F), cup F a b = - cup F b a := by
  first | exact @GlobalTheory.AbCoh.cup_anticomm | exact GlobalTheory.AbCoh.cup_anticomm | (intros; apply GlobalTheory.AbCoh.cup_anticomm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareOfSymmetricTensorRelations

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exteriorSq_of_symm_relations (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W)
    (hW : Module.finrank K W ≤ (Module.finrank K V).choose 2)
    (hrel : ∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) :
    (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧
      Function.Surjective (TensorProduct.lift β) ∧
      ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  classical
  set n := Module.finrank K V with hn
  have h0 : ∀ a b x : V, Function.update ![a, b] 0 x = ![x, b] := by
    intro a b x; ext i; fin_cases i <;> rfl
  have h1 : ∀ a b x : V, Function.update ![a, b] 1 x = ![a, x] := by
    intro a b x; ext i; fin_cases i <;> rfl
  let wb : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
    LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b])
      (by intro a₁ a₂ b
          rw [← h0 a₁ b (a₁ + a₂), AlternatingMap.map_update_add]; simp only [h0])
      (by intro c a b
          rw [← h0 a b (c • a), AlternatingMap.map_update_smul]; simp only [h0])
      (by intro a b₁ b₂
          rw [← h1 a b₁ (b₁ + b₂), AlternatingMap.map_update_add]; simp only [h1])
      (by intro c a b
          rw [← h1 a b (c • b), AlternatingMap.map_update_smul]; simp only [h1])
  let π : V ⊗[K] V →ₗ[K] ⋀[K]^2 V := TensorProduct.lift wb
  have hπt : ∀ a b, π (a ⊗ₜ b) = exteriorPower.ιMulti K 2 ![a, b] := by
    intro a b; simp [π, wb]
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span K 2 V, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    refine ⟨m 0 ⊗ₜ m 1, ?_⟩
    rw [hπt]; congr 1; ext i; fin_cases i <;> rfl
  have hswap : ∀ x y : V, exteriorPower.ιMulti K 2 ![x, y] = -exteriorPower.ιMulti K 2 ![y, x] := by
    intro x y
    rw [← (exteriorPower.ιMulti K 2).map_swap ![y, x] (show (0 : Fin 2) ≠ 1 by decide)]
    congr 1; ext i; fin_cases i <;> rfl
  have hdiag : ∀ x : V, exteriorPower.ιMulti K 2 ![x, x] = 0 := by
    intro x
    exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)
  let b := Module.finBasis K V
  let bt := b.tensorProduct b
  let r : V ⊗[K] V →ₗ[K] ⋀[K]^2 V :=
    bt.constr K (fun p => if p.1 < p.2 then exteriorPower.ιMulti K 2 ![b p.1, b p.2] else 0)
  have hrb : ∀ i j, r (b i ⊗ₜ b j) = if i < j then exteriorPower.ιMulti K 2 ![b i, b j] else 0 := by
    intro i j
    rw [← Module.Basis.tensorProduct_apply, Module.Basis.constr_basis]
  have hr : r ∘ₗ (LinearMap.id - (TensorProduct.comm K V V).toLinearMap) = π := by
    apply bt.ext; rintro ⟨i, j⟩
    simp only [bt, Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, map_sub, hrb, hπt]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h; simp [hdiag]
    · simp [h, lt_asymm h, hswap (b i) (b j)]
  have hS : ∀ t, TensorProduct.comm K V V t = t → π t = 0 := by
    intro t ht
    rw [← hr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ht,
      sub_self, map_zero]
  set L := TensorProduct.lift β with hLdef
  have hle : LinearMap.ker L ≤ LinearMap.ker π := fun t ht => hS t (hrel t ht)
  have hVV : Module.finrank K (V ⊗[K] V) = n * n := Module.finrank_tensorProduct
  have hext : Module.finrank K (⋀[K]^2 V) = n.choose 2 := by rw [exteriorPower.finrank_eq]
  have hπk := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hext, hVV] at hπk
  have hLk := LinearMap.finrank_range_add_finrank_ker L
  rw [hVV] at hLk
  have hLr : Module.finrank K (LinearMap.range L) ≤ Module.finrank K W := Submodule.finrank_le _
  have hNeq : LinearMap.ker L = LinearMap.ker π :=
    Submodule.eq_of_le_of_finrank_le hle (by
      generalize n * n = m at hπk hLk
      generalize n.choose 2 = k at hπk hW
      omega)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [hNeq] at hLk
    generalize n * n = m at hπk hLk
    generalize n.choose 2 = k at hπk hW
    omega
  refine ⟨?_, hL, fun t ht => ?_⟩
  · refine ⟨(π.quotKerEquivOfSurjective hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hNeq.symm).trans (L.quotKerEquivOfSurjective hL)), ?_⟩
    intro a c
    rw [← hπt, ← LinearMap.quotKerEquivOfSurjective_apply_mk π hπ, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, hLdef, TensorProduct.lift.tmul]
  · have : t ∈ LinearMap.ker L := hNeq ▸ hS t ht
    exact this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareOfSymmetricTensorRelationsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations : ∀ (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W), Module.finrank K W ≤ (Module.finrank K V).choose 2 → (∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) → (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧ Function.Surjective (TensorProduct.lift β) ∧ ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  first | exact @GlobalTheory.exteriorSq_of_symm_relations | exact GlobalTheory.exteriorSq_of_symm_relations | (intros; apply GlobalTheory.exteriorSq_of_symm_relations <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.WedgeSq

theorem exists_fin_sum_tmul {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (t : V ⊗[K] W) : ∃ (n : ℕ) (x : Fin n → V) (y : Fin n → W), t = ∑ i, x i ⊗ₜ[K] y i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | add s t hs ht =>
    obtain ⟨n, x, y, rfl⟩ := hs
    obtain ⟨m, x', y', rfl⟩ := ht
    exact ⟨n + m, Fin.append x x', Fin.append y y', by simp [Fin.sum_univ_add]⟩

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

variable {K : Type} [Field K]

theorem overPullbackStructureSheaf_cohomology_cup {Y A : Over (Sp K)} (f : Y ⟶ A) (a b : HO1 A.hom) :
    structureSheafH2Pullback f (cup (OAff A.hom) a b) = cup (OAff Y.hom) (pO1 f a) (pO1 f b) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 K K A.left Y.left A.hom Y.hom (RingHom.id K) f.left (ovw f)).1 a b

variable (A : Over (Sp K)) [GrpObj A]

abbrev mixed : HO1 A.hom →ₗ[K] HO1 A.hom →ₗ[K] HO2 (A ⊗ A).hom :=
  (cup (OAff (A ⊗ A).hom)).compl₁₂ (pO1 (fst A A)) (pO1 (snd A A))

theorem defect_eq (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom) :
    structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t) - structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      - structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      = TensorProduct.lift (mixed A) (t - TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul, map_sub, overPullbackStructureSheaf_cohomology_cup, hp a, hp b, map_add (f := _),
      LinearMap.add_apply, LinearMap.compl₁₂_apply]
    rw [GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm K _ (OAff (A ⊗ A).hom) (pO1 (snd A A) a) (pO1 (fst A A) b)]
    abel
  | add s t hs ht =>
    have e : s + t - TensorProduct.comm K _ _ (s + t)
        = (s - TensorProduct.comm K _ _ s) + (t - TensorProduct.comm K _ _ t) := by
      rw [map_add (f := _)]; abel
    rw [e, map_add (TensorProduct.lift (mixed A)), ← hs, ← ht]
    simp only [map_add (f := _)]
    abel

theorem mixed_injective [IsSeparated A.hom] [QuasiCompact A.hom] (u : HO1 A.hom ⊗[K] HO1 A.hom)
    (hu : TensorProduct.lift (mixed A) u = 0) : u = 0 := by
  obtain ⟨n, x, y, rfl⟩ := exists_fin_sum_tmul u
  refine GlobalTheory.T.kunneth_cup_tensor_injective K A A inferInstance inferInstance inferInstance inferInstance n x y ?_

  simpa [map_sum] using hu

theorem symm_of_prim [IsSeparated A.hom] [QuasiCompact A.hom] (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom)
    (ht : structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t)
      = structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
        + structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)) :
    TensorProduct.comm K _ _ t = t := by
  have h0 := defect_eq A hp t
  rw [ht, add_sub_cancel_left, sub_self] at h0
  exact (sub_eq_zero.1 (mixed_injective A _ h0.symm)).symm

end GlobalTheory.AbCoh.WedgeSq


open GlobalTheory.AbCoh.WedgeSq in
theorem GlobalTheory.AbCoh.wedgeO_noPrimO2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  intro K _ _ A _ g hab hsm
  haveI : IsProper A.hom := hab.proper
  haveI hsep : IsSeparated A.hom := inferInstance
  haveI hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨-, hprim, -⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hab hsm
  obtain ⟨n, D, hD, hcov⟩ := GlobalTheory.AbCoh.WedgeSq.exists_fin_affine_cover A.hom
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D hsep hD hcov
  obtain ⟨hfin, h1, h2⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hab hsm (Fin n) D hD hcov
  haveI := hfin 1
  haveI := hfin 2
  haveI : Module.Finite K (HO1 A.hom) := Module.Finite.equiv e1.symm
  haveI : Module.Finite K (HO2 A.hom) := Module.Finite.equiv e2.symm
  have hdim : Module.finrank K (HO2 A.hom) ≤ (Module.finrank K (HO1 A.hom)).choose 2 := by
    rw [e2.finrank_eq, e1.finrank_eq, h1]; exact h2
  have hrel : ∀ t : HO1 A.hom ⊗[K] HO1 A.hom, TensorProduct.lift (cup (OAff A.hom)) t = 0 →
      TensorProduct.comm K _ _ t = t := fun t ht ↦ symm_of_prim A hprim t (by simp [ht])
  obtain ⟨hw, hsurj, hsym⟩ := GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations K (HO1 A.hom) (HO2 A.hom) (cup (OAff A.hom)) hdim hrel
  refine ⟨hw, fun z hz ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hsurj z
  exact hsym t (symm_of_prim A hprim t hz)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2Statement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  first | exact @GlobalTheory.AbCoh.wedgeO_noPrimO2 | exact GlobalTheory.AbCoh.wedgeO_noPrimO2 | (intros; apply GlobalTheory.AbCoh.wedgeO_noPrimO2 <;> assumption)
end
end
