module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOntoStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormFromEquivariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForm_from_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → Function.Injective Jm → (∀ p ∈ ValC (gramC J emb) lam, ∃ ξ, Jm ξ = p) → ∀ g ∈ AdForms S emb lam, ∃ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) ∧ ∀ y : UPts σ J (FiniteAdeleRing (𝓞 F) F), g y = Jm (φ (Φ.symm (y * h0⁻¹))) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm
    hψ hK hχ hrat hint hinj hsurj g hg

  have hval : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_inf.mp hg).2 z (Set.mem_univ z)
  have hfun := (Submodule.mem_inf.mp hg).1
  choose pre hpre using fun z => hsurj (g z) (hval z)
  refine ⟨fun x => pre (Φ x * h0), ?_, ?_⟩
  · intro γ x κ
    obtain ⟨gr, hgrU, hgr⟩ := hrat γ
    apply hinj
    rw [hpre, LinearMap.map_smulₛₗ]
    funext y
    obtain ⟨y', hy'⟩ := exists_isTr' emb gr y
    rw [Pi.smul_apply, hint γ gr hgr (pre (Φ x * h0)) y y' hy', hpre]

    have hconj : (starRingEnd ℂ) ((((ψ κ)⁻¹ : ℂˣ) : ℂ)) = ((ψ κ : ℂˣ) : ℂ) := by
      rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ κ), Complex.conj_conj]
    rw [smul_eq_mul, hconj]
    have hk : ((h0⁻¹ * Φ κ.1 * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U :=
      (hK κ.1).1 κ.2
    have hx : (Φ (ιf γ * x * κ.1) * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
        Φ (ιf γ) * (Φ x * h0) * (h0⁻¹ * Φ κ.1 * h0) := by
      simp only [map_mul]; group
    have key := hfun gr hgrU (Φ x * h0) (Φ (ιf γ * x * κ.1) * h0) ⟨_, hk⟩
      (by rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, hgr]) y y' hy'
    rw [key, ← hχ κ.1 κ.2 hk]
  · intro y
    rw [hpre]
    congr 1
    simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjLinearOntoOfInjectiveOfLeRange

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValues

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValuesStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportCoeffMap_bijective_onto_values : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F), Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  first | exact @GlobalTheory.transport_J_bijective_onto | exact GlobalTheory.transport_J_bijective_onto | (intros; apply GlobalTheory.transport_J_bijective_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatch

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDict_bij_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  intro D X u F Tr hK hσ hL
  obtain ⟨hψ, -, hEq, hDet, hOnto⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨hJinj, hJsurj⟩ := GlobalTheory.T.transportCoeffMap_bijective_onto_values D X u F Tr
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have hcls := (GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hσ hL).1
    have h1 : ∀ c, shP X u T.1 (Tr.hc c) = 0 := by
      intro c
      apply hJinj
      rw [map_zero]
      funext y
      have := congrFun (congrFun hT c) (F.val0.eY.symm y)
      simpa [colDictL, dictA] using this
    apply hDet T
    intro x
    obtain ⟨c, ⟨γ, κ, hx⟩, -⟩ := hcls x
    rw [hx, hEq, h1, map_zero, smul_zero]
  · intro φ hφ
    rw [Formalism.L2.Forms.Mu0_iff F.val0] at hφ
    obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hφ
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
    obtain ⟨hΓ, -, hs⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
    have hKm : ∀ h : Hfin X u, h ∈ Ku X u hK ↔ ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U :=
      fun h => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).1
    have hχ : ∀ (h : Hfin X u) (hk : h ∈ Ku X u hK) (hy : ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U), ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) :=
      fun h hk hy => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).2 hk hy
    have hπ : ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E),
        (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g →
        ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
          Formalism.L2.Forms.IsTr (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1) y' y →
          Tr.J (piRep X u (iotaI X u γ) ξ) y = Tr.J ξ y' := by
      intro γ g e ξ y y' hy
      have h2 := hs γ g e
      exact Tr.J_eqv (iotaI X u γ) (iotaI X u γ).2 ξ y y' (by rw [h2]; exact hy)
    rw [Formalism.L2.Forms.lamT_zero] at hJsurj
    obtain ⟨φ', hφ'eq, hφ'g⟩ := GlobalTheory.adForm_from_equivariant _ _ (Formalism.L2.Forms.sigD D) _ _ _ _ _ F.cls0.lev
      (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 _
      (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ hKm hχ hΓ hπ hJinj hJsurj g hg
    obtain ⟨T, hT⟩ := hOnto φ' hφ'eq
    refine ⟨T, ?_⟩
    funext c z
    have hc : Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := (hΦ _ _).1 (Tr.hc_rep c)
    have e1 := congrFun (congrFun hres c) (F.val0.eY z)
    have e2 := hφ'g (F.cls0.y c)
    have e3 : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c := (MulEquiv.symm_apply_eq Φ).2 hc.symm
    rw [e3] at e2
    show Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY z) = φ c z
    rw [hT, ← e2]
    simpa [Formalism.L2.Forms.res] using e1

end GlobalTheory.St
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatchStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnDictionary_bijective_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  first | exact @GlobalTheory.St.colDict_bij_of_levelMatch | exact GlobalTheory.St.colDict_bij_of_levelMatch | (intros; apply GlobalTheory.St.colDict_bij_of_levelMatch <;> assumption)
end
end
