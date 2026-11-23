module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.Columns.RecLevelSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupIdentificationFixedPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiLevelPairCompatibleOfColumnLevelsStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LevelsFace

theorem level_ext'₂ {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {L L' : LevelP Pg r ℂ}
    (h : ∀ g, g ∈ L.H ↔ g ∈ L'.H) (h' : ∀ g hg hg', L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩) : L = L' := by
  obtain ⟨H, c⟩ := L
  obtain ⟨H', c'⟩ := L'
  obtain rfl : H = H' := Subgroup.ext h
  obtain rfl : c = c' := MonoidHom.ext fun g => h' g.1 g.2 g.2
  rfl

theorem chi_ofLocal_map' {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K] (σ : K →+* ℂ)
    (Hl : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (f : ∀ PP : Pg, Hl PP →* Multiplicative (kP PP.1))
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (g g' : G0 Pg r) (e : g = g') (hg : g ∈ Subgroup.pi Set.univ Hl)
    (hg' : g' ∈ Subgroup.pi Set.univ Hl) :
    Units.map σ.toMonoidHom ((LevelP.ofLocal Hl fun PP => addCharHom (ψ PP.1) (f PP)).chi ⟨g, hg⟩) =
      (LevelP.ofLocal Hl fun PP => addCharHom (σ.toMonoidHom.compAddChar (ψ PP.1)) (f PP)).chi ⟨g', hg'⟩ := by
  subst e
  refine ((congrArg (Units.map σ.toMonoidHom) (MonoidHom.finsetProd_apply _ _ _)).trans (map_prod _ _ _)).trans
    (Eq.trans ?_ (MonoidHom.finsetProd_apply _ _ _).symm)
  exact Finset.prod_congr rfl fun PP _ => Units.ext rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem levels_of_eq (hI : I.Ok) {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) (hId : IsPlacewiseIdentity X (px := px) eG) :
    ∃ ψ0 : ∀ PP : Pl X.toD7.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
      levPOf eG X.toD7.what₂.embLL (lev0 I) (chr0 I) = P0 Pg X.toD7.R.r ψ0 ∧
      ∃ π : Equiv.Perm (Fin X.toD7.R.r), IsSymOrd X.toD7.R.rS X.toD7.R.k π ∧
        (∀ g, g ∈ (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).H ↔
          reord π g ∈ (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).H) ∧
        ∀ g hg hg', (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).chi ⟨g, hg⟩ =
          (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).chi ⟨reord π g, hg'⟩ := by
  subst hPg
  have hs : ∀ g, eG.symm g = g := fun g =>
    funext fun w => (hId (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  have hle : X.toD7.R.k + X.toD7.R.rS ≤ X.toD7.R.r := by
    have := Formalism.L2.Col.r_eq_sym X.toD7.R
    omega
  refine ⟨fun PP => X.B.embLL.toMonoidHom.compAddChar (psiC I PP), fun PP hP h => ?_, level_ext'₂ (fun g => ?_)
    fun g hg hg' => ?_, (Formalism.L2.Col.symPerm X.toD7.R.r X.toD7.R.k X.toD7.R.rS).symm, fun a => ?_, fun g => ?_, fun g hg hg' => ?_⟩
  · have h1 : psiC I PP = 1 :=
      by
        ext x
        exact X.B.embLL.injective ((DFunLike.congr_fun h x).trans (map_one _).symm)
    rw [psiC_of_mem I hP] at h1
    exact hI.ch_ok.psi_zero_nontrivial_character _ h1
  · show eG.symm g ∈ lev0 I ↔ _
    rw [hs]
    exact Iff.rfl
  · exact chi_ofLocal_map' X.B.embLL _ _ (psiC I) _ _ (hs g) hg hg'
  · rw [Formalism.L2.Col.symPerm_symm_val hle]
    unfold Formalism.L2.Col.symIdxInv
    split_ifs <;> omega
  · show eG.symm g ∈ (Formalism.L2.Col.rPsymF I.Ch).grp ↔ _
    rw [hs]
    show g ∈ Subgroup.pi Set.univ _ ↔ reord _ g ∈ Subgroup.pi Set.univ _
    simp only [Subgroup.mem_pi]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    show g w ∈ Formalism.L2.Col.HPsymF _ _ _ _ ↔ _
    rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap]
    exact Iff.rfl
  · apply Units.ext
    have key : ∀ (w : (X.B.primes px).vGs) (M M' : GL (Fin X.toD7.R.r) (kP w.1)) (e : M' = Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS M)
        (hM : M ∈ Formalism.L2.Col.HPsymF (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS)
        (hM' : M' ∈ unipSym (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k),
        X.B.embLL ((Formalism.L2.Col.chiSymF (I.Ch.psi0 w) X.toD7.R.r X.toD7.R.k X.toD7.R.rS ⟨M, hM⟩ : X.B.LLˣ) : X.B.LL) =
          X.B.embLL (psiC I w.1 (Multiplicative.toAdd (symHom (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k ⟨M', hM'⟩))) := by
      intro w M M' e hM hM'
      subst e
      rw [Formalism.L2.Col.chiSymF_apply, Formalism.L2.Col.chiSym_eq_symHom _ _ _ _ _ hM', psiC_of_mem I w.2]
      rfl
    show X.B.embLL (((Formalism.L2.Col.rPsymF I.Ch).chr ⟨eG.symm g, hg⟩ : X.B.LLˣ) : X.B.LL) = _
    rw [Formalism.L2.Col.LevFam.chr_apply, Units.coe_prod, map_prod]
    erw [MonoidHom.finsetProd_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact key w _ _ (congrArg (fun h : G0 (X.B.primes px).vGs X.toD7.R.r =>
      Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS (h w)) (hs g)).symm _ _

theorem levelsL_face0 : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  intro X px I hX U Xg tr L eG hI hL hId
  exact levels_of_eq X I hI hL.Pg eG hId

end GlobalTheory.Mem.R3.LevelsFace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  first | exact @GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | exact GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | (intros; apply GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem addChar_pow_natCard_eq_one {A L : Type} [AddGroup A] [CommMonoid L] (ψ : AddChar A L) (c : A) :
    ψ c ^ Nat.card A = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem mem_Ks_of_pow_g (B : Base) (k : Fin 2) {x : B.LL} (hx : x ^ B.host.g k = 1) : x ∈ B.Ks := by
  have hp := B.host.g_prime k
  obtain ⟨z, hzK, hz⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
  have hne : B.host.g k * (B.host.g k - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (B.host.g k * (B.host.g k - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g k * (B.host.g k - 1)) := ⟨hne⟩
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_mul, hx, one_pow])
  rw [← hj]
  exact pow_mem hzK j

theorem chr0_mem_Ks : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I),
    ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  classical
  intro B px I p
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok B px).2.1
  unfold chr0 P0 LevelP.ofLocal
  letI : IsOneApply (lev0 I →* B.LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (lev0 I →* B.LLˣ) := ⟨fun _ _ _ => rfl⟩
  erw [prod_apply, Units.coe_prod]
  refine B.Ks.prod_mem fun PP _ => ?_
  have hk : ∃ k, PP.1 ∈ (B.primes px).vG k := by
    have h : PP.1 ∈ (B.primes px).vG 0 ∪ (B.primes px).vG 1 := by
      have h0 := PP.2
      unfold Formalism.L2.Col.Primes.vGs at h0
      convert h0
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hw⟩ := hk
  refine mem_Ks_of_pow_g B k ?_
  have hc : Nat.card (kP PP.1) = B.host.g k := by
    have h := hPr.vG_norm k PP.1 hw
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
    exact h
  rw [← hc]
  exact addChar_pow_natCard_eq_one _ _

end GlobalTheory.Mem.R3
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.upperUnipotentGenericCharacter_mem_integralField : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I), ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  first | exact @GlobalTheory.Mem.R3.chr0_mem_Ks | exact GlobalTheory.Mem.R3.chr0_mem_Ks | (intros; apply GlobalTheory.Mem.R3.chr0_mem_Ks <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Grp

theorem coeff_conj_of_central {G : Type} [Group G] (e : MonoidAlgebra ℂ G) (he : ∀ x, x * e = e * x) (k g : G) :
    e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_coeff_conj : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), GoodSet X (px := px) eR Xg → X.toD7.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g X.toD7.nd)) → ∀ a b : Gc X.B px, (idemOf Xg).coeff (a * b * a⁻¹) = (idemOf Xg).coeff b := by
  intro X px eR Xg hgood hc a b
  apply X.B.embLL.injective
  rw [hgood.2, hgood.2, map_mul eR, map_mul eR, map_inv eR]
  exact coeff_conj_of_central _ (Subalgebra.mem_center_iff.1 hc) _ _

theorem grp_levels_exist : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), IsPlacewiseIdentity X (px := px) eG ∧ GoodSet X (px := px) (eG.trans cG) Xg ∧ PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) ∧ (∀ g, (idemOf Xg).coeff g ∈ X.B.Ks) ∧ (∀ p, ((chr0 I p : X.B.LLˣ) : X.B.LL) ∈ X.B.Ks) ∧ ∀ tr, IdemClass (D := X.toD7) (famR X I hX U Xg tr).A ∧ Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 ∧ ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I hX U L hI hG hL
  obtain ⟨eG, cG, plg, iso, hid, hpl, hdiv, hbc⟩ := GlobalTheory.T.exists_finiteGroupIdentification_fixedPlaces X px I U L hI hG hL
  obtain ⟨Xg, hgood, hKs⟩ := GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField X px (eG.trans cG)
  refine ⟨eG, cG, Xg, hid, hgood, GlobalTheory.T.psiLevelPairCompatible_of_columnLevels X px I U L eG cG plg iso hI hL hid hpl hbc, hKs, GlobalTheory.T.upperUnipotentGenericCharacter_mem_integralField X.B px I,
    fun tr => ⟨?_, GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel X px I hX U Xg tr L eG hI hL hid, plg, iso, hpl, hdiv, hbc⟩⟩
  exact idemOf_coeff_conj X px (eG.trans cG) Xg hgood hG.cen

end GlobalTheory.Mem.R3.Grp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_finite_group_goodSet_levels_characters : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), IsPlacewiseIdentity X (px := px) eG ∧ GoodSet X (px := px) (eG.trans cG) Xg ∧ PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) ∧ (∀ g, (idemOf Xg).coeff g ∈ X.B.Ks) ∧ (∀ p, ((chr0 I p : X.B.LLˣ) : X.B.LL) ∈ X.B.Ks) ∧ ∀ tr, IdemClass (D := X.toD7) (famR X I hX U Xg tr).A ∧ Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 ∧ ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  first | exact @GlobalTheory.Mem.R3.Grp.grp_levels_exist | exact GlobalTheory.Mem.R3.Grp.grp_levels_exist | (intros; apply GlobalTheory.Mem.R3.Grp.grp_levels_exist <;> assumption)
end
end
