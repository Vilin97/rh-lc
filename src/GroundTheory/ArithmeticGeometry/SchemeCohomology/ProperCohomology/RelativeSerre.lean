module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Immersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AcyclicLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreAffine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {Y : Scheme.{u}} (G : Y.Modules)

lemma eq_of_forall_resF {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens} (hle : ∀ k, W k ≤ U)
    (hcov : U ≤ iSup W) (m m' : Γ(G, U)) (h : ∀ k, resF G (hle k) m = resF G (hle k) m') :
    m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (modulesAb G) W U (fun k => homOfLE (hle k)) hcov m m' h

lemma exists_resF_eq_of_compatible {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens}
    (hle : ∀ k, W k ≤ U) (hcov : U ≤ iSup W) (σ : ∀ k, Γ(G, W k))
    (hσ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) :
    ∃ m : Γ(G, U), ∀ k, resF G (hle k) m = σ k := by
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesAb G) W U
    (fun k => homOfLE (hle k)) hcov σ
    (fun k l => hσ k l)
  exact ⟨m, hm⟩

variable [G.IsQuasicoherent]

lemma basicOpen_resO_le {U W : Y.Opens} (hWU : W ≤ U) (h : Γ(Y, U)) :
    Y.basicOpen (resO hWU h) ≤ Y.basicOpen h := by
  rw [Scheme.basicOpen_res]
  exact inf_le_right

theorem qcoh_exists_pow_smul_eq_zero_of_isCompact {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (h : Γ(Y, U)) (m : Γ(G, U)) (hm : resF G (Y.basicOpen_le h) m = 0) :
    ∃ e : ℕ, h ^ e • m = 0 := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have hle : ∀ k : Us, (k : Y.Opens) ≤ U := fun k => hUeq ▸ le_sSup k.2
  have key : ∀ k : Us, ∃ e : ℕ, resO (hle k) h ^ e • resF G (hle k) m = 0 := fun k =>
    qcoh_exists_pow_smul_eq_zero G (hUs k.2) (resO (hle k) h) (resF G (hle k) m) (by
      rw [resF_resF, ← resF_resF G (Y.basicOpen_le h) (basicOpen_resO_le (hle k) h), hm, map_zero])
  choose e he using key
  have := Fintype.ofFinite Us
  refine ⟨Finset.univ.sup e, eq_of_forall_resF G (fun k : Us => (k : Y.Opens)) hle
    (by rw [hUeq, sSup_eq_iSup']) _ _ fun k => ?_⟩
  have hk : e k ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ k)
  rw [map_zero, resF_smul, map_pow, ← Nat.sub_add_cancel hk, pow_add, mul_smul, he k, smul_zero]

theorem qcoh_exists_res_eq_of_qcqs {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (hU' : IsQuasiSeparated (U : Set Y)) (h : Γ(Y, U)) (m : Γ(G, Y.basicOpen h)) :
    ∃ (e : ℕ) (m' : Γ(G, U)), resF G (Y.basicOpen_le h) m' = resO (Y.basicOpen_le h) h ^ e • m := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have := Fintype.ofFinite Us
  let W : Us → Y.Opens := fun k => k
  have hle : ∀ k, W k ≤ U := fun k => hUeq ▸ le_sSup k.2
  have hcov : U ≤ iSup W := by rw [hUeq, sSup_eq_iSup']

  have loc : ∀ k, ∃ (e : ℕ) (mk : Γ(G, W k)),
      resF G (Y.basicOpen_le (resO (hle k) h)) mk =
        resO (Y.basicOpen_le (resO (hle k) h)) (resO (hle k) h) ^ e •
          resF G (basicOpen_resO_le (hle k) h) m := fun k =>
    qcoh_exists_res_eq G (hUs k.2) (resO (hle k) h) (resF G (basicOpen_resO_le (hle k) h) m)
  choose e mk hmk using loc
  set N := Finset.univ.sup e
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ k, Γ(G, W k), ∀ k,
      resF G (Y.basicOpen_le (resO (hle k) h)) (σ k) =
        resO ((basicOpen_resO_le (hle k) h).trans (Y.basicOpen_le h)) h ^ N •
          resF G (basicOpen_resO_le (hle k) h) m := by
    refine ⟨fun k => resO (hle k) h ^ (N - e k) • mk k, fun k => ?_⟩
    have hk : e k ≤ N := Finset.le_sup (Finset.mem_univ k)
    rw [resF_smul, hmk, smul_smul]
    simp only [map_pow, resO_resO]
    rw [← pow_add, Nat.sub_add_cancel hk]

  have pair : ∀ k l, ∃ e' : ℕ, resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h ^ e' •
      (resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) -
        resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) = 0 := by
    intro k l
    have hkl : IsCompact ((W k ⊓ W l : Y.Opens) : Set Y) :=
      hU' _ _ (hle k) (W k).2 (hUs k.2).isCompact (hle l) (W l).2 (hUs l.2).isCompact
    refine qcoh_exists_pow_smul_eq_zero_of_isCompact G hkl _ _ ?_
    have hb : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle k) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_left
    have hb' : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle l) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_right
    rw [map_sub, resF_resF, resF_resF, sub_eq_zero,
      ← resF_resF G (Y.basicOpen_le (resO (hle k) h)) hb,
      ← resF_resF G (Y.basicOpen_le (resO (hle l) h)) hb', hσ k, hσ l, resF_smul, resF_smul,
      resF_resF, resF_resF, map_pow, map_pow, resO_resO, resO_resO]
  choose e' he' using pair
  set N' := Finset.univ.sup (fun kl : Us × Us => e' kl.1 kl.2)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ∀ k, Γ(G, W k), ∀ k, τ k = resO (hle k) h ^ N' • σ k :=
    ⟨fun k => resO (hle k) h ^ N' • σ k, fun _ => rfl⟩
  have hτ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (τ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (τ l) := by
    intro k l
    have hkl : e' k l ≤ N' := Finset.le_sup (f := fun kl : Us × Us => e' kl.1 kl.2)
      (Finset.mem_univ (k, l))
    rw [hτdef, hτdef, resF_smul, resF_smul, map_pow, map_pow, resO_resO, resO_resO, ← sub_eq_zero,
      ← smul_sub, ← Nat.sub_add_cancel hkl, pow_add, mul_smul, he' k l, smul_zero]
  obtain ⟨m', hm'⟩ := exists_resF_eq_of_compatible G W hle hcov τ hτ
  refine ⟨N' + N, m', ?_⟩

  refine eq_of_forall_resF G (fun k => Y.basicOpen (resO (hle k) h))
    (fun k => basicOpen_resO_le (hle k) h) ?_ _ _ fun k => ?_
  · intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hcov (Y.basicOpen_le h hx))
    refine Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hk, hx⟩
  · rw [resF_resF, ← resF_resF G (hle k) (Y.basicOpen_le (resO (hle k) h)), hm', hτdef, resF_smul,
      hσ k, resF_smul, smul_smul]
    simp only [map_pow, resO_resO, ← pow_add]

theorem isQuasicoherent_pushforward_of_qcqs {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens))
    (fun V => V.2) (iSup_affineOpens_eq_top Y) ?_ ?_
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hqs : IsQuasiSeparated ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) :=
      f.isQuasiSeparated_preimage V.2.isQuasiSeparated
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ Y.basicOpen g), ∃ (e : ℕ) (m' : Γ(F, f ⁻¹ᵁ (V : Y.Opens))),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m' =
        f.app (Y.basicOpen g) (resO (Y.basicOpen_le g) g ^ e) • m
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq_of_qcqs F hc hqs (f.app V g) (resF F hb.ge m)
    refine ⟨e, m', ?_⟩
    have h2 := congrArg (resF F hb.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, map_pow, resO_resO] at h2
    rw [h2, map_pow, app_resO]
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ (V : Y.Opens)),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m = 0 →
        ∃ e : ℕ, f.app V (g ^ e) • m = 0
    intro m hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero_of_isCompact F hc (f.app V g) m (by
      have h2 := congrArg (resF F hb.ge) hm
      rw [resF_resF, map_zero] at h2
      exact h2)
    exact ⟨e, by rw [map_pow]; exact he⟩

end

end GroundTheory.Arith.SchemeCoh
end
end

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

lemma embed_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.snd _ _ = ψ ∣_ V ≫ hV.isoSpec.hom := by
  letI := baseAlgebra A hV
  rw [← cancel_mono hV.fromSpec, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι]
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_snd (N := N) A hV
  have hq : pullback.snd (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)))
      hV.fromSpec ≫ hV.fromSpec = overV A hV ≫ pullback.snd _ _ := pullback.condition.symm
  simp only [embed, Category.assoc]
  rw [reassoc_of% hp, hq, reassoc_of% hc, pullback.lift_snd, ← Category.assoc, restrictIso_hom_fst]

lemma app_eqToHom_apply {X X' : Scheme.{u}} (ψ : X' ⟶ X) {U U' : X.Opens} (hU : U' = U)
    {W W' : X'.Opens} (h1 : W = ψ ⁻¹ᵁ U') (h2 : W' = W) (b : Γ(X, U)) :
    X'.presheaf.map (eqToHom h2).op (X'.presheaf.map (eqToHom h1).op
      (ψ.app U' (X.presheaf.map (eqToHom hU).op b))) =
      X'.presheaf.map (eqToHom (h2.trans (h1.trans (by rw [hU])))).op (ψ.app U b) := by
  subst hU
  subst h1
  subst h2
  simp

attribute [local instance] algebraOfOver

lemma algebraMap_overBase {V : X.Opens} (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI := overBase i ψ h hV
    X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(X', (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      ψ.app V b := by
  letI := overBase i ψ h hV
  have s1 : algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b = (ψ ∣_ V).appTop (V.topIso.inv b) := by
    change (embed i ψ h hV ≫ pullback.snd _ _).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [embed_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (app_eqToHom_apply ψ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp


omit [X.Over (Spec (.of A))] in
lemma smul_restrict_top (M : X'.Modules) (U : X'.Opens) (a : Γ(U.toScheme, ⊤))
    (y : Γ(M.restrict U.ι, ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
      ((modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y) =
      X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
        (a : Γ(X', U.ι ''ᵁ ⊤)) •
        M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
          (y : Γ(M, U.ι ''ᵁ ⊤)) := by
  have e1 : (modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y =
      restrictTop (X := U.toScheme) ⊤ a • y := rfl
  have e2 : restrictTop (X := U.toScheme) ⊤ a = a := by
    simp [restrictTop]; rfl
  have e3 : (a • y : Γ(M.restrict U.ι, ⊤)) =
      ((U.ι.appIso ⊤).inv a • (@id Γ(M, U.ι ''ᵁ ⊤) y) : Γ(M, U.ι ''ᵁ ⊤)) := rfl
  rw [e1, e2, e3, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Scheme.Modules.map_smul M (eqToHom (Scheme.Opens.ι_image_top U).symm) a y

def H0ToSections {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward ψ).obj M, V) :=
  letI := overBase i ψ h hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add (f := _)]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (smul_restrict_top M (ψ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overBase i ψ h hV b)).trans ?_
      exact (smul_pushforward ψ M b _).symm }

lemma H0ToSections_bijective {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    Function.Bijective (H0ToSections i ψ h hV M) := by
  letI := overBase i ψ h hV
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop).bijective

theorem finite_sections_pushforward {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Module.Finite Γ(X, V) (Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0) →
      Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward ψ).obj M, V) := by
  letI := overBase i ψ h hV
  intro hfin
  exact Module.Finite.of_surjective (H0ToSections i ψ h hV M) (H0ToSections_bijective i ψ h hV M).2

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end
end

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelativeSerre

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

attribute [local instance] algebraOfOver

namespace ProjScheme

theorem exists_relativeSerre {A : Type u} [CommRing A] [IsNoetherianRing A] {X X' : Scheme.{u}}
    [X.Over (Spec (.of A))] [X'.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [CompactSpace X] [IsLocallyNoetherian X] {N : ℕ} (i : X' ⟶ projectiveSpace A N)
    [IsClosedImmersion i] [i.IsOver (Spec (.of A))] (ψ : X' ⟶ X) [ψ.IsOver (Spec (.of A))]
    (G : X'.Modules) (hG : IsCoherent G) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsCoherent ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)) ∧
      ∀ p : ℕ, Nonempty (Sheaf.H.{u} (modulesAb (ProjScheme.twist i G n)) p ≃ₗ[A]
        Sheaf.H.{u} (modulesAb ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n))) p) := by
  classical
  have h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) := by
    rw [CategoryTheory.comp_over ψ (Spec (.of A))]
    exact CategoryTheory.comp_over i (Spec (.of A))
  have : X.IsSeparated := ⟨by
    rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  have : QuasiCompact (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ (X ↘ Spec (.of A))
  have : QuasiSeparated (ψ ≫ (X ↘ Spec (.of A))) := by
    rw [← h]
    infer_instance
  have : QuasiSeparated ψ := QuasiSeparated.of_comp ψ (X ↘ Spec (.of A))

  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun U : X.affineOpens => (U : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU⟩ := Opens.mem_iSup.1
        (show x ∈ ⨆ U : X.affineOpens, (U : X.Opens) by rw [iSup_affineOpens_eq_top X]; trivial)
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  let ι := { U // U ∈ t }
  let V : ι → X.Opens := fun a => a.1.1
  have hVaff1 : ∀ a, IsAffineOpen (V a) := fun a => a.1.2
  have hV : iSup V = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
    obtain ⟨hUt, hxU⟩ := Set.mem_iUnion.1 hU
    exact Opens.mem_iSup.2 ⟨⟨U, hUt⟩, hxU⟩

  let W : Finset ι → X.Opens := fun S => ⨅ a : S, V a
  have hWaff : ∀ S : Finset ι, S.Nonempty → IsAffineOpen (W S) := fun S hS => by
    have : Nonempty S := hS.to_subtype
    exact IsAffineOpen.iInf fun a => hVaff1 a
  have hWtuple : ∀ (m : ℕ) (s : Fin (m + 1) → ι),
      (⨅ a, V (s a)) = W (Finset.univ.image s) := fun m s => by
    apply le_antisymm
    · exact le_iInf fun b => by
        obtain ⟨a, -, ha⟩ := Finset.mem_image.1 b.2
        exact (iInf_le _ a).trans (le_of_eq (congrArg V ha))
    · exact le_iInf fun a => iInf_le (fun b : (Finset.univ.image s : Finset ι) => V b)
        ⟨s a, Finset.mem_image_of_mem s (Finset.mem_univ a)⟩
  have hWsingle : ∀ a : ι, W {a} = V a := fun a => by
    apply le_antisymm
    · exact iInf_le (fun b : ({a} : Finset ι) => V b) ⟨a, Finset.mem_singleton_self a⟩
    · exact le_iInf fun b => le_of_eq (congrArg V (Finset.mem_singleton.1 b.2).symm)

  have key : ∀ S : Finset ι, ∃ n₁ : ℕ, S.Nonempty → ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton (Sheaf.H.{u}
        (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ W S).ι)) (q + 1))) ∧
      Module.Finite Γ(X, W S) Γ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n), W S) := by
    intro S
    by_cases hS : S.Nonempty
    · have hA := hWaff S hS
      have : IsNoetherianRing Γ(X, W S) := IsLocallyNoetherian.component_noetherian ⟨_, hA⟩
      obtain ⟨n₁, hn₁⟩ := RelSerre.exists_vanishing_finite i ψ h hA G hG
      exact ⟨n₁, fun _ n hn => ⟨(hn₁ n hn).1,
        RelSerre.finite_sections_pushforward i ψ h hA _ (hn₁ n hn).2⟩⟩
    · exact ⟨0, fun h' => absurd h' hS⟩
  choose nS hnS using key
  refine ⟨Finset.univ.sup nS, fun n hn => ?_⟩
  have hle : ∀ S, nS S ≤ n := fun S => (Finset.le_sup (Finset.mem_univ S)).trans hn
  have : G.IsQuasicoherent := hG.1
  have : ((Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G n)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs ψ _
  refine ⟨?_, fun p => ?_⟩
  · refine isCoherent_of_affineCover _ V hVaff1 hV fun a => ?_
    have hfin := (hnS {a} (Finset.singleton_nonempty a) n (hle _)).2
    rw [hWsingle] at hfin
    exact hfin
  · have hVaff : ∀ (m : ℕ) (s : Fin (m + 1) → ι), IsAffineOpen (⨅ a, V (s a)) := fun m s =>
      IsAffineOpen.iInf fun a => hVaff1 (s a)
    refine ⟨HLinearEquivPushforwardOfAcyclic ψ A V hV hVaff (ProjScheme.twist i G n)
      ?_ p⟩
    intro m s q
    have h1 := (hnS (Finset.univ.image s) (Finset.univ_nonempty.image s) n (hle _)).1 q
    rw [← hWtuple] at h1
    exact h1

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
end
end
