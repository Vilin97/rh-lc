module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
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
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Mathlib.Tactic.Basify
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLatticeCohomologyVanish
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLatticeModel
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsLatticeFiniteStatement
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAtSmulMem

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem logAt_smul_mem : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X)
    (f : X.functionField) (η : abelian₂ X.functionField), RegAt y f → η ∈ logAt Z G a y → f • η ∈ logAt Z G a y := by
  intro X _ Z G a y f η hf hη
  unfold logAt spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨f * c, ?_, v, hv, ?_⟩
    · exact (show G.RegularAt y c from hc).regAt_mul hf
    · rw [smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LogDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelTwist

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {L : LB X} {r : L.ι → X.functionFieldˣ}

theorem sec_eq_of_not_gen {W : X.Opens} (hW : genericPoint X ∉ W) (s t : Γ(F, W)) : s = t :=
  sec_ext_of_cover (ι := PEmpty.{1}) (fun k => k.elim) (fun k => k.elim)
    (by intro x hx; exact (hW (gen_mem hx)).elim) (fun k => k.elim)

theorem val_resM (hM : LatModel M F) {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W)
    (s : Γ(F, U)) : hM.val W h (resM F e s) = hM.val U (e h) s :=
  hM.res U W e h s


variable (r) in
def tval (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) : Γ(twist F L, U) →+ V where
  toFun s := (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i)
  map_zero' := by rw [coord_zero, map_zero, smul_zero]
  map_add' s t := by rw [coord_add, map_add (f := _), smul_add]

theorem tval_apply (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(twist F L, U)) :
    tval r hM i hi U h s = (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i) := rfl

theorem val_coord_rel (hM : LatModel M F) {U : X.Opens} (s : Γ(twist F L, U)) (i j : L.ι)
    (hU : genericPoint X ∈ U) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    hM.val (U ⊓ L.U i) (memInf hU hi) (coord s i) =
      fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        hM.val (U ⊓ L.U j) (memInf hU hj) (coord s j) := by
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := memInf (memInf hU hi) hj
  have e := coord_rel s i j (W := U ⊓ L.U i ⊓ L.U j) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  have e1 := val_resM hM (inf_le_left : U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U i) hW (coord s i)
  have e2 := val_resM hM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U j) hW (coord s j)
  rw [← e1, ← e2, e, hM.smul, fnOf_resG]

theorem tval_eq (hM : LatModel M F) (hr : IsRatSec L r) {U : X.Opens} (h : genericPoint X ∈ U)
    (i j : L.ι) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j)
    (s : Γ(twist F L, U)) : tval r hM i hi U h s = tval r hM j hj U h s := by
  rw [tval_apply, tval_apply, val_coord_rel hM s i j h hi hj, Units.smul_def, Units.smul_def,
    smul_smul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j (memInf hi hj)]
  congr 1
  have hg : fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 :=
    ((L.g i j).isUnit.map (fnOf (L.U i ⊓ L.U j) (memInf hi hj))).ne_zero
  have hrj : (r j : X.functionField) ≠ 0 := (r j).ne_zero
  field_simp

end LatTwist

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {D : CartierDiv X} {L : LB X}
  {r : L.ι → X.functionFieldˣ}

theorem mem_of_mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : v ∈ latSec N U)
    {y : X} (hy : y ∈ U) : v ∈ N y :=
  AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv y) hy

theorem mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : ∀ y ∈ U, v ∈ N y) :
    v ∈ latSec N U :=
  AddSubgroup.mem_iInf.2 fun y => AddSubgroup.mem_iInf.2 fun hy => hv y hy

def twistModel (hP : Presents D L r)
    (hE : ∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y))
    (hM : LatModel M F) (i₀ : L.ι) (hi₀ : genericPoint X ∈ L.U i₀) :
    LatModel M' (twist F L) where
  val U h := tval r hM i₀ hi₀ U h
  inj U h := by
    intro s t e
    refine sec_ext fun i => ?_
    by_cases hi : genericPoint X ∈ L.U i
    · have e' : tval r hM i hi U h s = tval r hM i hi U h t := by
        rw [← tval_eq hM hP.isRatSec h i₀ i hi₀ hi, ← tval_eq hM hP.isRatSec h i₀ i hi₀ hi]
        exact e
      rw [tval_apply, tval_apply] at e'
      exact hM.inj (U ⊓ L.U i) (memInf h hi) (MulAction.injective _ e')
    · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i => hi hh.2) _ _
  range U h := by
    ext v
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine mem_latSec fun y hy => ?_
      obtain ⟨i, hi⟩ := exists_chart hP.isLB y
      have hgi : genericPoint X ∈ L.U i := gen_mem hi
      rw [tval_eq hM hP.isRatSec h i₀ i hi₀ hgi, hE y (r i) _ (hP.isEqn i y hi), tval_apply,
        ← Units.smul_def, smul_inv_smul]
      have hw : hM.val (U ⊓ L.U i) (memInf h hgi) (coord s i) ∈ (hM.val (U ⊓ L.U i) (memInf h hgi)).range :=
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hM.range] at hw
      exact mem_of_mem_latSec hw (memInf hy hi)
    · intro hv
      have key : ∀ i, ∃ t : Γ(F, U ⊓ L.U i),
          ∀ hi : genericPoint X ∈ L.U i, hM.val (U ⊓ L.U i) (memInf h hi) t = r i • v := by
        intro i
        by_cases hi : genericPoint X ∈ L.U i
        · have hm : r i • v ∈ latSec M (U ⊓ L.U i) := mem_latSec fun y hy => by
            rw [Units.smul_def, ← hE y (r i) v (hP.isEqn i y hy.2)]
            exact mem_of_mem_latSec hv hy.1
          rw [← hM.range (U ⊓ L.U i) (memInf h hi)] at hm
          obtain ⟨t, ht⟩ := hm
          exact ⟨t, fun _ => ht⟩
        · exact ⟨0, fun h' => (hi h').elim⟩
      choose t ht using key
      have hmem : t ∈ Twist.secGroup F L U := by
        intro i j
        by_cases hij : genericPoint X ∈ L.U i ⊓ L.U j
        · have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := (memInf (memInf h hij.1) hij.2)
          apply hM.inj (U ⊓ L.U i ⊓ L.U j) hW
          rw [hM.smul, val_resM, val_resM, fnOf_resG, ht i hij.1, ht j hij.2, Units.smul_def,
            Units.smul_def, smul_smul, hP.isRatSec i j hij]
        · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j => hij (memInf hh.1.2 hh.2)) _ _
      exact ⟨mkSec t hmem, by rw [tval_apply, coord_mkSec, ht i₀ hi₀, inv_smul_smul]⟩
  res U W e h s := by
    change tval r hM i₀ hi₀ W h (resM (twist F L) e s) = tval r hM i₀ hi₀ U (e h) s
    rw [tval_apply, tval_apply, coord_resM, val_resM]
  smul U h a s := by
    change tval r hM i₀ hi₀ U h (a • s) = fnOf U h a • tval r hM i₀ hi₀ U h s
    rw [tval_apply, tval_apply, coord_smul, hM.smul, fnOf_resG, Units.smul_def, Units.smul_def,
      smul_smul, smul_smul, mul_comm]

end LatTwist

theorem nonempty_latModel_twist : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M M' : X → AddSubgroup V) (F : X.Modules) (D : CartierDiv X)
    (L : LB X) (r : L.ι → X.functionFieldˣ), Presents D L r →
    (∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y)) →
    LatModel M F → Nonempty (LatModel M' (twist F L)) := by
  intro X _ V _ _ M M' F D L r hP hE hM
  obtain ⟨i₀, hi₀⟩ := exists_chart hP.isLB (genericPoint X)
  exact ⟨LatTwist.twistModel hP hE hM i₀ hi₀⟩

end GlobalTheory.LogDR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemSpanFormsOfMulMem

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlas

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem spanForms_eq_bot_of_isCoord {K : Type} [Field K] {n : ℕ} {x : Fin n → Kˣ} (hx : IsCoord x)
    (M : Set K) (H : Set Ω[K⁄ℤ]) {a : ℕ} (ha : n < a) : spanForms M H a = ⊥ := by
  let bs : Module.Basis (Fin n) K Ω[K⁄ℤ] := Module.Basis.mk hx.1 hx.2.ge
  haveI : Module.Finite K Ω[K⁄ℤ] := Module.Finite.of_basis bs
  have hfr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  refine eq_bot_iff.2 ((AddSubgroup.closure_le _).2 ?_)
  rintro η ⟨c, -, v, -, rfl⟩
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ v hv, smul_zero]
  exact AddSubgroup.zero_mem _

theorem logAt_eq_bot_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (Z : Set X) (G : CartierDiv X) {a : ℕ} (ha : n < a) (y : X) :
    logAt Z G a y = ⊥ := by
  have hg : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, -⟩ := (Opens.mem_iSup).1 hg
  exact spanForms_eq_bot_of_isCoord ((𝒜.chart i).chart _ (𝒜.gen i)).coord _ _ ha

theorem cechFam_eq_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) :
    cechFam 𝒜 G a = cechFam 𝒜 G (n + 1) := by
  funext s
  simp only [cechFam, logSec, latSec, logAt_eq_bot_of_lt 𝒜 _ G ha,
    logAt_eq_bot_of_lt 𝒜 _ G (Nat.lt_succ_self n)]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem exists_cechZero_cechFam_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  intro k _ X _ f hf C _ E n ι _ _ 𝒜 H B R hH
  haveI : IsProper f := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  haveI : X.IsSeparated := by
    constructor
    rw [show terminal.from X = f ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  letI := algebraΓOfHom f
  have key : ∀ (j : Fin B) (a : Fin (n + 2)), ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ b : ℕ, 0 < b →
      DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
    intro j a
    obtain ⟨F, ⟨lm⟩⟩ := GlobalTheory.T.exists_lattice_model X (logAt (suppAll E) (R j) a)
      (fun y g v hg hv => logAt_smul_mem X _ _ _ y g v hg hv)
    haveI : IsFiniteQC F := GlobalTheory.T.log_forms_lattice_finite X E 𝒜 (R j) a F lm
    have hev := eventually_subsingleton_coh_twistZ_of_isProjOver (f := f) (fun _ => rfl) F hf hH
    obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
    refine ⟨q₀, fun q hq b hb => ?_⟩
    obtain ⟨lm'⟩ := nonempty_latModel_twist X (logAt (suppAll E) (R j) a)
      (logAt (suppAll E) (q • H + R j) a) F (q • H) (toLB (q • H)) _ (presents_toLB _)
      (fun y g v hD => by rw [add_comm]; exact logtwist X _ _ _ _ y g v hD) lm
    haveI : IsFiniteQC (twist F (toLB (q • H))) := isFiniteQC_twist (isLB_toLB _)
    have hc := GlobalTheory.T.cech_lattice_cohomology_vanish X (logAt (suppAll E) (q • H + R j) a) (twist F (toLB (q • H))) 𝒜.U lm'
      𝒜.affine 𝒜.gen 𝒜.cover b hb
    refine hc.2 ?_
    haveI hs : Subsingleton (coh (twist F (lbZPow (toLB H) (q : ℤ))) b) := hq₀ q hq b hb
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F (isLB_toLB (q • H)) (isLB_lbZPow (isLB_toLB H) q)
      (by rw [cls_lbZPow (isLB_toLB H), ← toPic_apply, ← toPic_apply, map_nsmul, natCast_zsmul])
    exact (cohOn.mapIso k ⊤ b e).injective.subsingleton
  choose q₁ hq₁ using key
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun p : Fin B × Fin (n + 2) => q₁ p.1 p.2)
  refine ⟨Q, fun q hq j a b hb => ?_⟩
  by_cases ha : a ≤ n + 1
  · exact hq₁ j ⟨a, by omega⟩ q ((hQ (j, ⟨a, by omega⟩)).trans hq) b hb
  · rw [cechFam_eq_of_lt 𝒜 _ (by omega : n < a)]
    exact hq₁ j ⟨n + 1, by omega⟩ q ((hQ (j, ⟨n + 1, by omega⟩)).trans hq) b hb

end GlobalTheory.LogDR
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlasStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.serre_vanishing_snc_atlas : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | exact _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | (intros; apply _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add <;> assumption)
end
end
