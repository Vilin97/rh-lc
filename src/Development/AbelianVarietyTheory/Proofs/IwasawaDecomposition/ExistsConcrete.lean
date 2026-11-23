module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
public import Formalism.LocalToGlobal.HermitianColumns.FullSym
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TieEmbeddingCastLevelTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.AwayChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
open scoped TensorProduct

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adelic_ext {n : ℕ} (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g = bc (prV (E := E) v) h) : g = h := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub]
  have h1 := congrArg Units.val (H w)
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV] at h1
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  rw [this, sub_self]

theorem exists_trivial_on {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ s, bc (prV (E := E) v) k = 1) ∧
      ∀ v ∉ s, bc (prV (E := E) v) k = bc (prV (E := E) v) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have hne : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 k) = bc (prV (E := E) w) k := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      rfl
    refine ⟨Formalism.UG.P.afsplitU v 1 k, Formalism.UG.P.afsplitU_mem v σ J 1 k (one_mem _) hk, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h; exact Formalism.UG.P.afsplit_right1 w 1 k
      · rw [hne w h]; exact h1 w ((Finset.mem_insert.1 hw).resolve_left h)
    · rw [Finset.mem_insert, not_or] at hw
      rw [hne w hw.1]; exact h2 w hw.2

theorem finite_over (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_away_mem (S : StepLevel F E σ J T f bad) (p : ℕ) (hp : p ≠ 0)
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) g ∈ S.Uloc w) :
    ∃ κ : S.U, (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) g := by
  obtain ⟨k, hk, h1, h2⟩ := exists_trivial_on σ J (finite_over (F := F) p hp).toFinset g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
  refine ⟨⟨k, (S.U_eq k).2 ⟨hk, fun v => ?_⟩⟩, h1, h2⟩
  by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v hv]; exact one_mem _
  · rw [h2 v hv]; exact hw v hv

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A ℂ) (x : A) : IsIntegral ℤ (ψ x) := by
  have h : ψ x ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact IsIntegral.of_pow Nat.card_pos (by rw [h]; exact isIntegral_one)

theorem chi_isIntegral {gp : Fin 2 → ℕ} {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t 0 skip fc zl) (κ : S.U) : IsIntegral ℤ ((S.chi κ : ℂˣ) : ℂ) := by
  rw [X.chi_eq κ]
  refine IsIntegral.prod _ fun i _ => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun h => ?_
  haveI : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one, ← AddChar.map_neg_eq_inv]
  exact addChar_isIntegral _ _

end Adelic

theorem exists_inv_char {U LL O Kf : Type} [Group U] [Field LL] [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (χ : U →* ℂˣ) (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ c : U →* Oˣ, ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ algebraMap O Kf ((c κ : Oˣ) : O) * e r = 1 := by
  choose r hr o ho using h
  have r1 : r 1 = 1 := embLL.injective (by rw [hr]; simp)
  have rm : ∀ a b, r (a * b) = r a * r b := fun a b => embLL.injective (by rw [map_mul, hr, hr, hr]; simp)
  let o' : U →* O :=
    { toFun := o
      map_one' := hinj (by rw [ho, r1, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, ho, ho, ho, rm, map_mul]) }
  refine ⟨o'.toHomUnits⁻¹, fun κ => ⟨r κ, hr κ, ?_⟩⟩
  rw [← ho κ, ← map_mul]
  have : o κ = ((o'.toHomUnits κ : Oˣ) : O) := rfl
  rw [this, MonoidHom.inv_apply, Units.inv_mul, map_one]

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem exists_psiTied {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E sp.cm.sig J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hp : p ≠ 0) (hk : R.k = n)
    (hJ : ∀ x y, J x y = sp.gram0 (Fin.cast hk.symm x) (Fin.cast hk.symm y))
    (hU : ∀ v, S.Uloc v = (L.Uloc v).map (reGL hk _).toMonoidHom)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ, PsiTied S L p hk embLL e ψ := by
  obtain ⟨c, hc⟩ := exists_inv_char hinj S.chi embLL e h
  have hex : ∀ a : Formalism.L2.Herm.awayFrom₂ L p, ∃ κ : S.U,
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1) := by
    intro a
    obtain ⟨h2, h3⟩ := (mem_awayP_iff L p a.1).1 a.2
    refine exists_away_mem S p hp _ (reGL_mem_UPts hk sp.cm.sig sp.gram0 J hJ _ _ h2) fun w hw => ?_
    rw [bc_reGL, hU w]
    exact Subgroup.mem_map.2 ⟨_, h3 w hw, rfl⟩
  choose κ h1 h2 using hex
  have huniq : ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (k : S.U),
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k.1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) k.1 = bc (prV (E := E) w) (reGL hk _ a.1)) → κ a = k := by
    intro a k k1 k2
    refine Subtype.ext (adelic_ext _ _ fun v => ?_)
    by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [h1 a v hv, k1 v hv]
    · rw [h2 a v hv, k2 v hv]
  let K : Formalism.L2.Herm.awayFrom₂ L p →* S.U := MonoidHom.mk' κ fun a b => by
    refine huniq _ _ (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.coe_mul, map_mul, h1 a v hv, h1 b v hv, mul_one]
    · rw [Subgroup.coe_mul, map_mul, h2 a v hv, h2 b v hv, Subgroup.coe_mul, map_mul, map_mul]
  refine ⟨c.comp K, fun a k k1 k2 => ?_⟩
  obtain rfl := huniq a k k1 k2
  exact hc (κ a)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar



theorem exists_psi : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) → (∀ u, LevelZeroCharacterRational T u) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))ˣ,
      PsiTied (LL := D.what₂.LL) (O := ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
        (Kf := KfRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ((T u).cls0).lev (L0 u)
        (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ψ := by
  intro D L0 T hJ hψ u w _
  refine exists_psiTied ((T u).cls0).lev (L0 u) _ (D.what₂.places.resChar_prime w).ne_zero (rank_eq_first_level D.R) (Formalism.L2.G.Cmp.gramN_zero D)
    (hJ u).Uloc_eq Subtype.val_injective _ _ fun κ => ?_
  obtain ⟨r, hr⟩ := chiRatAll_rec T u (hψ u) κ
  refine ⟨r, hr, (embRec_int D w _ r).1 ((val_nonneg_iff D w r).2 ?_)⟩
  have h1 : IsIntegral ℤ (D.what₂.embLL r) := hr ▸ chi_isIntegral ((T u).glev0) κ
  have h2 : IsIntegral ℤ r := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 h1
  exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (⟨r, h2⟩ : 𝓞 D.what₂.LL)

end GlobalTheory.Mem.AwayChar
end
end
end

-- Source module: Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieStd

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField Matrix

namespace Formalism.L2.G

theorem stdB_core {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (h : V → V → E)
    (c : V ≃ₗ[E] (Fin n → E)) (hc : ∀ x y, h x y = hform σ J (c x) (c y)) (b : Module.Basis (Fin n) E V)
    (hb : ∀ a a', h (b a) (b a') = if a = a' then 1 else 0) (L0 : Submodule (𝓞 E) V)
    (hL : L0 = Submodule.span (𝓞 E) (Set.range b)) :
    ∃ B : GL (Fin n) E, cT σ B.1 * J * B.1 = 1 ∧
      ∀ x : Fin n → E, x ∈ L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
        ∀ a, ((B⁻¹ : GL (Fin n) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  let b' : Module.Basis (Fin n) E (Fin n → E) := b.map c
  let M : Matrix (Fin n) (Fin n) E := (Pi.basisFun E (Fin n)).toMatrix b'
  let M' : Matrix (Fin n) (Fin n) E := b'.toMatrix (Pi.basisFun E (Fin n))
  have h1 : M * M' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : M' * M = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  let B : GL (Fin n) E := ⟨M, M', h1, h2⟩
  have hM : ∀ i a, M i a = c (b a) i := fun i a => by
    simp [M, b', Module.Basis.toMatrix_apply]
  refine ⟨B, ?_, fun x => ?_⟩
  · ext a a'
    have := hb a a'
    rw [hc] at this
    rw [Matrix.one_apply, ← this]
    simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, B, hM, Finset.sum_mul]
    rw [Finset.sum_comm]
  · have e1 : L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Submodule.span (𝓞 E) (Set.range b') := by
      rw [hL, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e1, Module.Basis.mem_span_iff_repr_mem]
    have e2 : (B⁻¹ : GL (Fin n) E).1 *ᵥ x = b'.repr x := by
      show M' *ᵥ x = b'.repr x
      have h3 := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun E (Fin n)) b' x
      have h4 : ((Pi.basisFun E (Fin n)).repr x : Fin n → E) = x := funext fun i => Pi.basisFun_repr E (Fin n) x i
      rw [h4] at h3
      exact h3
    rw [e2]
    rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_form_frame_coordinates (D : D7) (x y : (D.sp.X 0).V) :
    (D.sp.X 0).hT x y = hform (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
      (crdN D 0 (Nat.zero_le _) x) (crdN D 0 (Nat.zero_le _) y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm]
  unfold hform
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  rfl

theorem exists_stdB (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B := by
  obtain ⟨b, hb, hL⟩ := h
  obtain ⟨B, h1, h2⟩ := stdB_core (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (fun x y => (D.sp.X 0).hT x y) (crdN D 0 (Nat.zero_le _)) (hermitian_form_frame_coordinates D)
    (b.reindex (finCongr (rankN D 0 (Nat.zero_le _))))
    (fun a a' => by
      simp only [Module.Basis.reindex_apply]
      rw [hb]
      simp)
    (D.sp.X 0).L0 (by rw [hL, Module.Basis.range_reindex])
  refine ⟨(reGL (rank_eq_first_level D.R) D.host.E).symm B, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact h1
  · rw [MulEquiv.apply_symm_apply]
    exact h2

theorem exists_stdB_of_tied (D : D7) (h : Formalism.L2.Herm.StdTied D) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B :=
  exists_stdB D (h.1 0 (Nat.zero_le _))

end Formalism.L2.G
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcrete

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack

namespace GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable (D : D7) (L0 : LevelData D)

def Companion : Prop :=
  ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
    (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0

def stdBasis (hS : Formalism.L2.Herm.StdTied D) : GL (Fin D.R.k) D.host.E := Classical.choose (exists_stdB_of_tied D hS)

theorem stdBasis_std (hS : Formalism.L2.Herm.StdTied D) : Cmp.StdB D (stdBasis D hS) := Classical.choose_spec (exists_stdB_of_tied D hS)

def placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  locIdStd D u w hg (Classical.choose (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)) (stdBasis D hS) (stdBasis_std D hS)
    (Classical.choose (hC u)) (Classical.choose_spec (hC u))

def embK (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg))

def embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))

theorem embK_embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (z : D.what₂.LL) : embK D L0 u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) = lamV (embAlg D L0 u w hg) (D.what₂.embLL z) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).1 z

def awayChar (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ :=
  Classical.choose (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg)

def gatOf (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (sc : Scale) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GAtP (D.what₂.places.resChar w) :=
  (packC D (fun u => L0 u) I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc 1 (D.what₂.places.resChar w))


theorem gatOf_d (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (I) (ψ) (sc : Scale) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (gatOf D L0 I ψ sc u w h).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
  have e := GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h (I u w h) (ψ u w h) (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))
  rw [pack_eq] at e
  exact e

section Main

variable {D L0}


theorem posOK_placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0)
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (packC D (fun u => L0 u) (placeId D L0 hS hC) ψ u w hg).posOK (embK D L0 u w hg) (embAlg D L0 u w hg) := by
  have e := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).2 (ψ u w hg)
  unfold LocPack.posOK at e ⊢
  exact e

end Main

section Main2

variable {D L0}

end Main2

theorem gPlTiedS_of {X : D7} {Gt : GatTies X} (H0 : Formalism.L2.Herm.Herm0 X)
    (hpl : ∀ u w hg (v : Fin (X.gat u w hg).P.nV) (s : Fin ((X.gat u w hg).P.n' v)) (x : 𝓞 X.host.F),
      x ∈ ((H0.g u w hg).pl v).1.asIdeal ↔
        (0 : WithTop ℤ) < X.what₂.places.val w (tauLL X (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap X.host.F X.host.E (x : X.host.F))))
    (B : Formalism.L2.Herm.HermColsCh X) (gS : Formalism.L2.Herm.SymmetricGroupCompatibility X B) (hB : B.lev0 = H0.lev0) (hg : HEq gS H0.g) :
    Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces X B gS Gt := by
  obtain ⟨l, g⟩ := H0
  dsimp only at hB hg hpl
  subst hB
  obtain rfl := eq_of_heq hg
  exact hpl

end GlobalTheory.Mem.ConcreteRecord
end
end
end
