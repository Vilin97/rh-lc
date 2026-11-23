module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunCount
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTripleLoc
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
public import Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunChar

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem unrAt_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 E)) : UnrAt (1 : Chr F E) w := fun x _ => by
  simp [locChar]

theorem charSt : CharSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hX v w hw hv z hz
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have hwT : w ∉ above E (X.T : Set (Pl F)) := fun hm => hv (h ▸ hm)
  have hev : Even (a' + a) := by rw [add_comm]; exact hX.geo.even
  have hres : ∀ b : (AF F)ˣ, (X.α * X.β) (ideleMap F E b) = (1 : Chr F E) (ideleMap F E b) := by
    intro b
    have hA : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resα b
    have hB : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resβ b
    rw [MonoidHom.mul_apply, MonoidHom.one_apply, ← Circle.coe_eq_one, Circle.coe_mul, hA, hB]
    split_ifs
    · simp
    · rw [← pow_add, hev.neg_one_pow]
  have key := GlobalTheory.InertChars.locIdele_eq_of_inert hw (X.α * X.β) 1 hres
    ((hX.chars.unrα w hwT).mul (hX.chars.unrβ w hwT)) (unrAt_one w)
  refine ⟨?_, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hX v w hw hv z hz⟩
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw, ← MonoidHom.mul_apply, key,
    MonoidHom.one_apply]

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open Formalism.UG (IsInertAt)
open GlobalTheory.LFun.InertChart (under_eq_iff)

namespace EvInv

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locChar_one {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : IsInertAt F E v w) {χ : Chr F E}
    (h1 : ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χ z = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  rw [PT.locChar_eq hw h H y, MonoidHom.one_apply]
  exact h1 _ (PT.locIdele_spec hw h y).1

end EvInv

open EvInv in
theorem evInvSt : EvInvSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hWl v w hw hχ ω ρ hR m Cy hL _ l hl h0 g hg φ hφ
  have hσ := hP.base.cm
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW hP hWl v
  obtain rfl : χWv = 1 := locChar_one hw hχ L.chW
  obtain ⟨c1, c2⟩ := PT.psi_good hP.base.std (hP.base.inert v w hw).2.2 L.psi
  have a1 := PT.isHerm_loc (v := v) hX
  have a2 := PT.isSkew_loc (v := v) hW
  have a3 := PT.isLagr_loc hσ hw hW hL
  have a4 := PT.isEv_of L hL.supp hl h0
  have fix := split_character_fixes_evaluation _ _ _ ψv (PT.isField_Ev hw) (PT.isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ l a1 a2 a3 L.weil a4
  obtain ⟨gv, -, e1, -, -⟩ := L.loc g hg 1 (one_mem_UAt W v)
  have e : ω (g, 1) φ = omv.comp (MonoidHom.inl _ _) gv φ :=
    (PT.actsX L hg e1 hφ _).1 ((hR.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)
  rw [e]
  exact fix gv φ hφ

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunFin

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK

theorem finSt_relIndex_le {G : Type} [Group G] {H K L : Subgroup G} (hKL : K ≤ L) (h : H.relIndex L ≠ 0) :
    H.relIndex K ≠ 0 := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_relIndex_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (b : GL (Fin n) (w.adicCompletion E)) :
    (KGL w (n := n) ⊓ (KGL w (n := n)).map (MulAut.conj b).toMonoidHom).relIndex (KGL w (n := n)) ≠ 0 := by
  obtain ⟨ho, hc⟩ := SatCompare.isOpen_isCompact_KGL w n
  have hcont : Continuous fun x : GL (Fin n) (w.adicCompletion E) => b⁻¹ * x * b :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine finSt_relIndex_nhds hc (U := (KGL w (n := n) : Set _) ∩ (fun x => b⁻¹ * x * b) ⁻¹' (KGL w (n := n) : Set _))
    ((ho.inter (ho.preimage hcont)).mem_nhds ⟨one_mem _, by simp [one_mem]⟩) fun k _ hk => ⟨hk.1, ?_⟩
  refine ⟨b⁻¹ * k * b, hk.2, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem finSt : FinSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw g hg
  classical
  have hv : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hv
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKH.Iwas.exists_frame hB.cm hw hv hc hW
  let Φ : UA σ W.J →* GL (Fin d) (w.adicCompletion E) :=
    (MulAut.conj a⁻¹).toMonoidHom.comp
      ((Units.map (RingHom.mapMatrix (PositivityTheory.ThKH.Iwas.piE hv)).toMonoidHom).comp (Subgroup.subtype _))
  have hΦ : ∀ x, ((Φ x : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (a⁻¹).1 * (mat x).map (PositivityTheory.ThKH.Iwas.piE hv) * a.1 := fun x => by
    simp [Φ, mat]
  have memK : ∀ x ∈ UAt σ W (evFin F v), x ∈ KSub σ W v ↔ Φ x ∈ KGL w (n := d) := fun x hx => by
    rw [mem_GLint_iff, ← map_inv, hΦ, hΦ]
    change (x ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat x *ᵥ y ∈ latW W v ∧ mat x⁻¹ *ᵥ y ∈ latW W v) ↔ _
    rw [← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha, ← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha]
    exact ⟨fun H => ⟨fun y hy => (H.2 y hy).1, fun y hy => (H.2 y hy).2⟩, fun H => ⟨hx, fun y hy => ⟨H.1 y hy, H.2 y hy⟩⟩⟩
  set K := KSub σ W v
  set H' := KGL w (n := d) ⊓ (KGL w (n := d)).map (MulAut.conj (Φ g)).toMonoidHom
  have h1 : (H'.comap Φ).relIndex K ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    refine finSt_relIndex_le ?_ (finSt_KGL w d (Φ g))
    rintro _ ⟨k, hk, rfl⟩
    exact (memK k hk.1).1 hk
  have h2 : H'.comap Φ ⊓ K ≤ conjInf K g := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨hk2, g⁻¹ * k * g, ?_, ?_⟩
    · have hx : g⁻¹ * k * g ∈ UAt σ W (evFin F v) := mul_mem_UAt (mul_mem_UAt (inv_mem_UAt hg) hk2.1) hg
      refine (memK _ hx).2 ?_
      obtain ⟨y, hy, ey⟩ := hk1.2
      have : Φ (g⁻¹ * k * g) = y := by
        rw [map_mul, map_mul, map_inv, ← ey]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]; exact hy
    · simp [MulAut.conj_apply, mul_assoc]
  have h3 : (H'.comap Φ ⊓ K).relIndex K ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
  intro h0
  exact h3 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K h2))

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  PositivityTheory.ThK.PT

namespace FunSieg

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

local instance charZeroFv {F : Type} [Field F] [NumberField F] (v : Pl F) : CharZero (Fv F v) :=
  charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv {F : Type} [Field F] [NumberField F] (v : Pl F) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero two_ne_zero

local instance modTopEv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

theorem siegSt : SiegSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW P hW v w hw _ ω ρ hR m Cy hL _ l hl p hp t hpt z hz hzt u hu φ hφ
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW P hW v
  have hσ := P.base.cm
  obtain ⟨r, s, hX⟩ := P.herm
  obtain ⟨r', s', hWs⟩ := P.skew
  obtain ⟨c1, c2⟩ := psi_good P.base.std (P.base.inert v w hw).2.2 L.psi
  have a1 := isHerm_loc (v := v) hX
  have a2 := isSkew_loc (v := v) hWs
  have a3 := isLagr_loc hσ hw hWs hL
  have R := siegel_transport _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ a1 a2 a3 L.weil.1
  obtain ⟨hv, ehv⟩ := exW L hp
  have eω : ω (1, p) φ = omv.comp (MonoidHom.inr _ _) hv φ :=
    (actsW L hp ehv hφ _).1 ((hR.acts 1 (one_mem_UAt X v) p hp φ hφ (ω (1, p) φ)).2 rfl)
  by_cases h0 : ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l φ ≠ 0
  · have hdet : IsUnit (t.map (compFin F E v)).det := by
      rw [← hzt]; exact (Units.map (compFin F E v).toMonoidHom z).isUnit
    let tv : GL (Fin m) (Ev E v) := ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit
    have htv : (tv : Matrix (Fin m) (Fin m) (Ev E v)) = t.map (compFin F E v) := rfl
    have hdt : Matrix.GeneralLinearGroup.det tv = Units.map (compFin F E v).toMonoidHom z :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, htv]; exact hzt.symm)
    have hpv : ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) * Cy.map (compFin F E v) =
        Cy.map (compFin F E v) * (tv : Matrix (Fin m) (Fin m) (Ev E v)) := by
      rw [show ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) = hv.1.1 from rfl, ← ehv, htv,
        ← Matrix.map_mul, ← Matrix.map_mul, hpt]
    have hu' : Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (Matrix.GeneralLinearGroup.det tv) = u :=
      Units.ext (by rw [hdt, hu]; rfl)
    have key := R l (Set.mem_univ _) (isEv_of L hL.supp hl h0).2 hv tv hpv φ hφ
    rw [eω, key, hu', hdt, L.chX z hz, Fintype.card_fin]
  · push Not at h0
    rw [h0 _ (hR.pres 1 (one_mem_UAt X v) p hp φ hφ), h0 φ hφ, mul_zero]

end FunSieg

theorem siegSt : SiegSt := FunSieg.siegSt

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.UnitLiftSt

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas

theorem unitLiftSt : UnitLiftSt := by
  intro F E _ _ _ _ _ v y
  have hab : ∀ a b : Ev E v, sgE E v a * sgE E v b = sgE E v (a * b) := fun a b => by
    have e := GlobalTheory.EmbChart.tensAt_mul_right (E := E) v a (sgE E v b)
    rw [comp_sgE] at e
    exact e
  have key : ∀ a b : Ev E v, (1 + sgE E v a) * (1 + sgE E v b) = 1 + sgE E v ((1 + a) * (1 + b) - 1) := fun a b => by
    have e : (1 + a) * (1 + b) - 1 = a + b + a * b := by ring
    rw [e, map_add (f := _), map_add (f := _), ← hab]
    ring
  refine ⟨⟨1 + sgE E v ((y : Ev E v) - 1), 1 + sgE E v (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1), ?_, ?_⟩, ?_, ?_⟩
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.mul_inv, sub_self, map_zero, add_zero]
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.inv_mul, sub_self, map_zero, add_zero]
  · change At (evFin F v) (1 + sgE E v _ - 1)
    rw [add_sub_cancel_left]
    exact at_sgE _
  · change compFin F E v (1 + sgE E v _) = _
    rw [map_add (f := _), map_one, comp_sgE]
    ring

theorem pInvSt : PInvSt := by
  intro F E _ _ _ _ _ σ d W v w hw m Cy hL p hp
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨hpU, t₀, ht₀⟩ := hp
  set φ := piE (F := F) (E := E) h with hφ
  have hpinv : (mat p⁻¹).map φ * (mat p).map φ = 1 := by
    rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

  have hfree : ∀ s : Fin m → w.adicCompletion E, Cy.map φ *ᵥ s = 0 → s = 0 := fun s hs => by
    obtain ⟨s', hs', e⟩ := vec_surj h s
    have h0 : Cy *ᵥ s' = 0 := vec_inj hw h (by rw [sub_zero]; exact at_mulVec_left hL.supp _) (by
      rw [piE_mulVec, e, hs]; funext i; simp)
    rw [← e, hL.free s' hs' h0]; funext i; simp
  have hdet : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → (t.map φ).det ≠ 0 := fun t ht hdt => by
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdt
    refine hs0 (hfree s ?_)
    have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t.map φ := by rw [← Matrix.map_mul, ht, Matrix.map_mul]
    have e2 : Cy.map φ *ᵥ s = (mat p⁻¹).map φ *ᵥ ((Cy.map φ * t.map φ) *ᵥ s) := by
      rw [← e1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hpinv, Matrix.one_mul]
    rw [e2, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hunit : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → IsUnit (t.map (compFin F E v)).det := fun t ht => by
    have e : (t.map (compFin F E v)).map (toCompl h) = t.map φ := by rw [Matrix.map_map]; rfl
    have hne : toCompl h (t.map (compFin F E v)).det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, e]; exact hdet t ht
    exact (MulEquiv.isUnit_map (RingEquiv.ofBijective (toCompl h) (toCompl_bijective hw h)).toMulEquiv).1
      (isUnit_iff_ne_zero.2 hne)
  refine ⟨⟨inv_mem_UAt hpU, ?_⟩, hunit⟩
  have hu : IsUnit (t₀.map φ).det := isUnit_iff_ne_zero.2 (hdet t₀ ht₀)
  obtain ⟨t', ht'a, ht'⟩ := mat_surj h (t₀.map φ)⁻¹
  refine ⟨t', mat_inj hw h (at_sub (at_mul_right _ hL.supp) (at_mul_left hL.supp _)) ?_⟩
  have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t₀.map φ := by rw [← Matrix.map_mul, ht₀, Matrix.map_mul]
  rw [Matrix.map_mul, Matrix.map_mul, ht']
  calc (mat p⁻¹).map φ * Cy.map φ = (mat p⁻¹).map φ * (Cy.map φ * (t₀.map φ * (t₀.map φ)⁻¹)) := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Cy.map φ * (t₀.map φ)⁻¹ := by
        rw [← Matrix.mul_assoc (Cy.map φ), ← e1, Matrix.mul_assoc, ← Matrix.mul_assoc ((mat p⁻¹).map φ), hpinv, Matrix.one_mul]

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunTop

section

@[expose] public section

namespace PositivityTheory.Sph

theorem sphFun_of_modSt (hM : ModSt) : SphFun :=
  sphFun_of countSt avgSt pInvSt unitLiftSt charSt evInvSt siegSt hM cartanSt2 finSt

end PositivityTheory.Sph
end
end
