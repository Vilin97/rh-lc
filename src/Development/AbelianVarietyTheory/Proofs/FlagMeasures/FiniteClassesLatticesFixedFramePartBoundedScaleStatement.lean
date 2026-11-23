module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometryClassesDefiniteHermitianBoundedScaStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.HermitianLattices.FinalNeighbourConstruct
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsComplHermitianOrthogonalOfTotallyPositiveStatement
public import Mathlib.Algebra.Module.Lattice.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryExtendOrthogonalByIdentity

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthExt

theorem hT_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT u v = 0 := by
  have := hv
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this u hu

theorem hT_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT v u = 0 := by
  have h1 := S.herm.eq u v
  rw [hT_orth_right S U hu hv] at h1
  simpa using h1.symm

theorem extend_isom : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  intro E _ _ _ S U hc g hg
  let e := Submodule.prodEquivOfIsCompl U (orth S U) hc
  let γ : S.V ≃ₗ[E] S.V := (e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e
  have hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V) := fun x => rfl
  have hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V) := fun x => by
    conv_lhs => rw [← e.apply_symm_apply x]
    rfl
  have key : ∀ (a b : U) (c d : ↥(orth S U)),
      S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d := by
    intro a b c d
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]
    ring
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro x y
    change S.hT (γ x) (γ y) = S.hT x y
    rw [hγ, hγ, key, hg, ← key, ← hx, ← hx]
  · intro u hu
    rw [hγ]
    have : e.symm u = (⟨u, hu⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩
    rw [this]; simp
  · intro w
    rw [hγ]
    have : e.symm w = (0, w) := Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w
    rw [this]; simp

end GlobalTheory.OrthExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryExtendOrthogonalByIdentityStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  first | exact @GlobalTheory.OrthExt.extend_isom | exact GlobalTheory.OrthExt.extend_isom | (intros; apply GlobalTheory.OrthExt.extend_isom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteLatticesBetweenOfSmulLe

section

@[expose] public section

open NumberField

namespace GlobalTheory

theorem finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  intro K V _ _ _ _ _ _ M hM N hN
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  let f : V →ₗ[𝓞 K] V := (((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hf : ∀ x, f x = (N : K)⁻¹ • x := fun x => rfl
  have hback : ∀ x : V, f ((N : K) • x) = x := by
    intro x; rw [hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]
  have hsm : ∀ x ∈ M, (N : K) • x ∈ M := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx N
  set D := M.map f with hD
  have hMD : M ≤ D := fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩
  have hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D} := by
    rintro Λ ⟨h1, h2⟩
    exact ⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩
  refine Set.Finite.subset ?_ hsub
  have h1 := Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr (hM.map f)
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      obtain ⟨m, hm, hq⟩ := q.2
      have : (((N : ℤ) • q : D.toAddSubgroup) : V) = m := by
        rw [AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
          smul_smul, mul_inv_cancel₀ hNK, one_smul]
      rw [this]
      exact hm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteLatticesBetweenOfSmulLeStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.finite_lattices_between_of_smul_le' : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  first | exact @GlobalTheory.finite_lattices_between_of_smul_le | exact GlobalTheory.finite_lattices_between_of_smul_le | (intros; apply GlobalTheory.finite_lattices_between_of_smul_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegersStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V), Submodule.IsLattice K Λ → ∀ W : Submodule K V, Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.isLattice_comap_subtype_ringOfIntegers | exact GlobalTheory.isLattice_comap_subtype_ringOfIntegers | (intros; apply GlobalTheory.isLattice_comap_subtype_ringOfIntegers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteClassesLatticesFixedFramePartBoundedScale

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatClassFin

theorem fg_of_le_fg {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    {N L : Submodule (𝓞 K) V} (hL : L.FG) (h : N ≤ L) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_of_le_right h]
  rw [← e]; exact h1.map _

theorem frame_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast i =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem classes_fin : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D T T' F F' hpos A N d c hN hd hc
  classical
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hcompl : IsCompl U W := GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos
  let hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E := (VS D).hT.domRestrict₁₂ W W
  have hWs : hW.IsSymm := (VS D).herm.domRestrict W
  have hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x) := fun x hx =>
    hpos x.1 x.2 (fun h => hx (Subtype.ext h))
  obtain ⟨s, hslat, hs⟩ := GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc
  let ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V := W.subtype.restrictScalars (𝓞 D.host.E)
  let Mof : Submodule (𝓞 D.host.E) ↥W → LV D := fun L => A ⊔ L.map ι
  let Sset : Set (LV D) :=
    ⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}
  have hfin : Sset.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun L _ => ?_
    by_cases hA : A.FG
    · by_cases hL : L.FG
      · refine (GlobalTheory.T.finite_lattices_between_of_smul_le' (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_
        rintro Λ' ⟨-, -, h1, h2⟩
        exact ⟨h1, h2⟩
      · exact Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)
    · exact Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)
  refine ⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩
  set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'
  have hL'lat : Submodule.IsLattice D.host.E L' := GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W
  have hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
    fun x hx y hy => hdΛ x.1 hx y.1 hy
  have hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) →
      (c : D.host.E) • y ∈ L' := by
    intro y hy
    show (c : D.host.E) • (y : (VS D).V) ∈ Λ
    exact hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)
  obtain ⟨M₀, hM₀s, g, hg, hgM⟩ := hs L' hL'lat hsc hdu
  have hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V) :=
    fun x y => hg x y
  obtain ⟨γ, hγi, hγU, hγW⟩ := GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity (VS D) U hcompl g hgiso
  have hγH : γ ∈ H0 F F' :=
    ⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)),
      fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩
  have hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ := fun x => by
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; rfl
  have hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U := fun a ha => by
    rw [← hAΛ] at ha; exact ⟨ha.1, ha.2⟩
  refine ⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩
  rw [Set.Finite.mem_toFinset]
  have hAfg : A.FG := by
    rw [← hAΛ]; exact fg_of_le_fg hΛ.fg inf_le_left
  have hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι := by
    intro w hw hwΛ
    have h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by rw [hgM]; exact hwΛ
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearEquiv.eq_symm_apply]
    show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w
    rw [hγW, LinearEquiv.apply_symm_apply]
  refine Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩
  · refine sup_le (fun a ha => ?_) ?_
    · rw [hmem, hγU a (hAsub a ha).2]; exact (hAsub a ha).1
    · rintro _ ⟨m, hm, rfl⟩
      rw [hmem]
      show γ ((m : ↥W) : (VS D).V) ∈ Λ
      rw [hγW]
      have h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by
        rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]; exact hm
      rw [hgM] at h1
      exact h1
  · intro x hx
    rw [hmem] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (hNΛ _ hx)
    have hx' : (N : D.host.E) • x = γ.symm u + γ.symm w := by
      rw [← map_add (f := _), huw, map_smul, LinearEquiv.symm_apply_apply]
    have hu' : γ.symm u = u := by
      rw [LinearEquiv.symm_apply_eq]; exact (hγU u hu.2).symm
    rw [hx', hu']
    refine Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)
    rw [← hAΛ]; exact hu

end GlobalTheory.LatClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteClassesLatticesFixedFramePartBoundedScaleStatement

section

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  first | exact @GlobalTheory.LatClassFin.classes_fin | exact GlobalTheory.LatClassFin.classes_fin | (intros; apply GlobalTheory.LatClassFin.classes_fin <;> assumption)
end
end
