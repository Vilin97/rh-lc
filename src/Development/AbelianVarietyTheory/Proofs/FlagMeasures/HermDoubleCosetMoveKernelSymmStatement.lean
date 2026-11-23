module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacterStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConstStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFamily_trace_volume_const : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  first | exact @GlobalTheory.HL.FamilyVol.family_vol | exact GlobalTheory.HL.FamilyVol.family_vol | (intros; apply GlobalTheory.HL.FamilyVol.family_vol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEq

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEqStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  first | exact @GlobalTheory.RefVol.main | exact GlobalTheory.RefVol.main | (intros; apply GlobalTheory.RefVol.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChangeStatement

section

@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_transport_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (Nice (A.map e.toAddMonoidHom) φ ↔ Nice A (fun w => φ (e w))) ∧ cint (A.map e.toAddMonoidHom) φ = cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (Nice A φ ↔ Nice A' φ) ∧ cint A' φ * (A.relIndex A' : ℂ) = cint A φ * (A'.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.Transport.cint_map_and_change | exact GlobalTheory.IdxInt.Transport.cint_map_and_change | (intros; apply GlobalTheory.IdxInt.Transport.cint_map_and_change <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymm

section

@[expose] public section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernSym

def flipMv (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :
    A × B × C ≃+ A × B × C where
  toFun w := (w.1, -w.2)
  invFun w := (w.1, -w.2)
  left_inv w := by simp
  right_inv w := by simp
  map_add' w w' := by
    ext <;> simp [add_comm]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem refA_map_flip (J : ℕ) (Λ : Submodule L.O S.V) :
    (S.refA J Λ).map (flipMv (S.V × S.V) S.V E).toAddMonoidHom = S.refA J Λ := by
  have key : ∀ w : S.MW, w ∈ S.refA J Λ → ((w.1, -w.2) : S.MW) ∈ S.refA J Λ := by
    intro w hw
    rw [Frames.refA, AddSubgroup.mem_prod] at hw ⊢
    exact ⟨hw.1, neg_mem hw.2⟩
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact key v hv
  · intro hw
    refine ⟨(w.1, -w.2), key w hw, ?_⟩
    show ((w.1, - -w.2) : S.MW) = w
    simp

theorem sOf_flip [CharZero F] (w : S.MW) (hs : S.sOf w + L.cj (S.sOf w) = S.h w.2.1 w.2.1) :
    S.sOf (w.1, -w.2) = L.cj (S.sOf w) := by
  have h1 : S.h (-w.2.1) (-w.2.1) = S.h w.2.1 w.2.1 := by
    simp [Frames.h, hf]
  have h2 : algebraMap F E 2⁻¹ + algebraMap F E 2⁻¹ = 1 := by
    rw [← map_add (f := _), ← map_one (algebraMap F E)]
    congr 1
    norm_num
  have h3 : L.cj (S.sOf w) = S.h w.2.1 w.2.1 - S.sOf w := by
    rw [← hs]; ring
  rw [h3]
  show algebraMap F E 2⁻¹ * S.h (-w.2.1) (-w.2.1) + -w.2.2 = _
  rw [h1, Frames.sOf]
  linear_combination (S.h w.2.1 w.2.1) * h2
end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mvTo_flip (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ Λ' : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hF : S.InFF β (j + 1) βJ d Λ) (hF' : S.InFF β (j + 1) βJ d Λ')
    (w : S.MW) (hw : S.MvTo (j + 1) d Λ Λ' w) : S.MvTo (j + 1) d Λ' Λ (w.1, -w.2) := by
  obtain ⟨hm, he⟩ := hw
  obtain ⟨Λ₁, h1, -, h3, h4, -⟩ :=
    GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF w.1.1 w.1.2 w.2.1 (S.sOf w) hm
  have hΛ : Λ₁ = Λ' := SetLike.coe_injective (h1.trans he.symm)
  subst hΛ
  have hs := sOf_flip S w hm.2.2.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · show S.IsMove (j + 1) d Λ₁ w.1.1 w.1.2 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h4 hF'
  · show (Λ : Set S.V) = S.moved Λ₁ w.1.1 (-w.2.1) (S.sOf (w.1, -w.2))
    rw [hs]
    exact h3.symm
end

theorem kern_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hr, hne⟩ := GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq L r k S j β βJ d Λ hT hF Λ' hT' hF'
  obtain ⟨hmap, hchg⟩ := @GlobalTheory.T.indexMeasureIntegral_transport_and_change S.MW _ S.MW _
  have e1 := (hmap (flipMv (S.V × S.V) S.V E) (S.refA (j + 1) Λ)
    (ind (S.MvTo (j + 1) d Λ' Λ))).2
  rw [refA_map_flip] at e1
  have e2 : (fun w => ind (S.MvTo (j + 1) d Λ' Λ) (flipMv (S.V × S.V) S.V E w)) =
      ind (S.MvTo (j + 1) d Λ Λ') := by
    funext w
    have hiff : S.MvTo (j + 1) d Λ' Λ (flipMv (S.V × S.V) S.V E w) ↔ S.MvTo (j + 1) d Λ Λ' w := by
      constructor
      · intro h
        have h' := mvTo_flip S j β βJ d Λ' Λ hT' hF' hF _ h
        have hw : (((flipMv (S.V × S.V) S.V E w).1, -(flipMv (S.V × S.V) S.V E w).2) : S.MW) = w := by
          show ((w.1, - -w.2) : S.MW) = w
          simp
        rwa [hw] at h'
      · intro h
        exact mvTo_flip S j β βJ d Λ Λ' hT hF hF' w h
    simp only [ind, hiff]
  rw [e2] at e1
  have e3 := (hchg (S.refA (j + 1) Λ) (S.refA (j + 1) Λ') (ind (S.MvTo (j + 1) d Λ' Λ)) hne
    (hr ▸ hne)).2
  rw [← hr] at e3
  have e4 := mul_right_cancel₀ (Nat.cast_ne_zero.mpr hne) e3
  unfold Frames.kern
  rw [e4, e1]

end GlobalTheory.HL.KernSym
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMoveKernelSymmStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermDoubleCosetMoveKernel_symm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → S.kern β (j + 1) βJ d Λ Λ' = S.kern β (j + 1) βJ d Λ' Λ := by
  first | exact @GlobalTheory.HL.KernSym.kern_symm | exact GlobalTheory.HL.KernSym.kern_symm | (intros; apply GlobalTheory.HL.KernSym.kern_symm <;> assumption)
end
end
