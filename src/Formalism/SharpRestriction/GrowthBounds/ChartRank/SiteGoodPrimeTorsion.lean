module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVin
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocMore
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypEvChain
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe
public import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude
public import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.IntWOfPow
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVinRec

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {j : ℕ}
  (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

structure LatTies (w : D.what₂.places.Pl) (Fo : FormsIn M (j + 1) hj) (β : Fo.Ch)
    (Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (j + 1)).rank → D.host.E)) : Prop where
  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T
  Lb_eq : (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) Lb
  lat : ∀ cl : {c // Fo.chOf c = β}, Submodule.IsFullLattice D.host.E (Fo.lat cl.1)
  chi : ∀ κ : (Fo.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ)



theorem latIn_of {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} {β : Fo.Ch}
    (hfr : FrRatJ (Lc.t β) Lc.B) (H : LatTies hj w Fo β (Lc.Lb β)) : LatIn (stepInOf hj Fo Lc pos) w β :=
  { prime := hg.1
    resChar := rfl
    siteGood_prime_torsion := H.siteGood_prime_torsion
    alg := fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a
    base := fun v t => frlat_re (rankN D (j + 1) hj) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (Lc.Lb β)
      Lc.B ((Lc.t β).fr _ ((X.g u w hg).pl v).2) (hfr _ _) ((Lc.t β).fr_lat _ ((X.g u w hg).pl v).2) (Fo.K β).lev.Lb H.Lb_eq t
    lat := H.lat
    chi := H.chi }



theorem valIntN_rec {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (HT : ∀ β, LocTies hj Fo Lc pos e β) (hS : BlockRationalityField) (hfrac : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf))
    (HL : ∀ β, LatTies hj w Fo β (Lc.Lb β)) : (stepInOf hj Fo Lc pos).ValIntN e w :=
  valIntN_of (stepInOf hj Fo Lc pos) e w (fun β => core_of hj (HT β)) hS hfrac hR0
    (fun β => latIn_of hj (HT β).frRat (HL β))

end Formalism.MainNotions.G.CmpJ.PValIntN

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFin

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf}


open Classical in
theorem finClasses_of (H : ∀ β, S.Core e β) (X : ChX S) : G.FinClasses := by
  intro a
  refine ⟨((Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c).attach.image
    (fun c => ((Finset.mem_filter.1 c.2).2).choose), ?_, ?_⟩
  · intro L hL
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hL
    exact ((Finset.mem_filter.1 c.2).2).choose_spec.1
  · intro L hL
    have hc : clsOf H a L ∈ (Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, L, hL, rfl⟩
    refine ⟨_, Finset.mem_image.2 ⟨⟨clsOf H a L, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have spec := ((Finset.mem_filter.1 hc).2).choose_spec
    obtain ⟨_, γ, hγ⟩ := (clsOf_iff H X a a _ L spec.1 hL).1 spec.2
    exact ⟨γ, hγ⟩

end Formalism.MainNotions.G.ChF

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypForms

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem isTr_inv_mul (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ1 γ2 : GL (Fin n) E)
    (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) := by
  intro τ
  show atInf emb ((γ1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ =
    atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
      (atInf emb ((γ2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [← Matrix.mul_assoc]
  congr 1
  simp only [atInf]
  rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]

def LawAt (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

theorem law_wd (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) (hv : LawAt S emb y0 v)
    (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * y0.1 * κ2.1) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    (S.chi κ1 : ℂ) * v (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) =
      (S.chi κ2 : ℂ) * v (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) := by
  have e0 : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ1⁻¹ * γ2) * y0.1 * (κ2 * κ1⁻¹ : S.U).1 := by
    have e' : y0.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1) * κ1.1⁻¹ := by group
    rw [e] at e'
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y0.1 = _ := e'
      _ = _ := by group
  rw [hv (γ1⁻¹ * γ2) ((UJ _ _).mul_mem ((UJ _ _).inv_mem h1) h2) (κ2 * κ1⁻¹) e0 _ _ (isTr_inv_mul emb hc γ1 γ2 h1 h2 z),
    map_mul, map_inv, Units.val_mul, ← mul_assoc, ← mul_assoc, mul_comm (S.chi κ1 : ℂ), mul_assoc (S.chi κ2 : ℂ), mul_comm ((S.chi κ1 : ℂˣ) : ℂ),
    Units.inv_mul, mul_one]


open Classical in
theorem exists_form_of_law (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ)
    (hV : v ∈ ValC (gramC J emb) lam) (hv : LawAt S emb y0 v) : ∃ g ∈ AdForms S emb lam, g y0 = v := by
  let Pd : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Prop := fun x =>
    ∃ q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) q.1.1 * y0.1 * q.2.1
  let g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x y =>
    if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0
  have gval : ∀ x (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 → ∀ y,
      g x y = (S.chi κ : ℂ) * v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
    intro x γ hγ κ e y
    have h : Pd x := ⟨(⟨γ, hγ⟩, κ), e⟩
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dite_eq_left h]
    exact law_wd S emb hc y0 v hv _ _ h.choose.1.2 hγ _ _ (h.choose_spec.symm.trans e) y
  have gzero : ∀ x, ¬ Pd x → ∀ y, g x y = 0 := by
    intro x h y
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dite_eq_right h]
  refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · intro γ' hγ' x x' κ' hx' y y' hy
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have e' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γ) * y0.1 * (κ * κ' : S.U).1 := by
        rw [hx', e, map_mul, Subgroup.coe_mul]; group
      rw [gval x γ hγ κ e, gval x' (γ' * γ) ((UJ _ _).mul_mem hγ' hγ) (κ * κ') e']
      have hfr : frameTranslate emb hc (γ' * γ)⁻¹ ((UJ _ _).inv_mem ((UJ _ _).mul_mem hγ' hγ)) y =
          frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y' := by
        apply Subtype.ext
        funext τ
        show atInf emb (((γ' * γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
          atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
        rw [hy τ, _root_.mul_inv_rev]
        simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rw [hfr, map_mul, Units.val_mul]
      ring
    · have hP' : ¬ Pd x' := by
        rintro ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩
        refine hP ⟨(⟨γ'⁻¹ * γ, (UJ _ _).mul_mem ((UJ _ _).inv_mem hγ') hγ⟩, κ * κ'⁻¹), ?_⟩
        show x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ'⁻¹ * γ) * y0.1 * (κ * κ'⁻¹ : S.U).1
        have e1 : x.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ')⁻¹ * x'.1 * κ'.1⁻¹ := by
          rw [hx']; group
        rw [e1, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [gzero x hP, gzero x' hP', mul_zero]
  · refine Submodule.mem_pi.2 fun x _ => ?_
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have : g x = (S.chi κ : ℂ) • fun y => v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
        funext y
        exact gval x γ hγ κ e y
      rw [this]
      exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ hV)
    · have : g x = 0 := by
        funext y
        exact gzero x hP y
      rw [this]
      exact Submodule.zero_mem _
  · funext y
    rw [gval y0 1 (UJ _ _).one_mem 1 (by rw [map_one]; simp)]
    have hfr : frameTranslate emb hc (1 : GL (Fin n) E)⁻¹ ((UJ _ _).inv_mem (UJ (σ : E →+* E) J).one_mem) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((1 : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [inv_one]
      simp [atInf]
    rw [hfr, map_one, Units.val_one, one_mul]

end Gen

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem formsOnClassOf (S : StepIn M i hi G) : FormsOnClassOf S := by
  intro β c v hv
  obtain ⟨g, hg, e⟩ := exists_form_of_law (S.K β).lev (embT D) (embedding_conj_compat D) (lamTG M i) ((S.K β).y c) v hv.1 hv.2
  exact Submodule.mem_map.2 ⟨res (embT D) (S.K β).y g, Submodule.mem_map.2 ⟨g, hg, rfl⟩, e⟩

end Formalism.MainNotions.G.ChF

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.SiteGoodPrimeTorsion

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ.PValIntN Formalism.MainNotions.G.CmpJ.PInvLe
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

section Step

variable {j : ℕ} (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}



structure StepTies (Fo : FormsIn M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch) (Gt : GatTies D) (c : LatCmp D) : Prop where

  frRat : ∀ β, FrRatJ (Lc.t β) Lc.B

  sameU : ∀ β, SameUlocJ hj (Fo.K β).lev (Lc.Uloc β)

  hypT : ∀ β, HypTJ (Lc.t β)

  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal

  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 * gramN D (j + 1) hj *
    (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 = 1

  psi : ∀ β, UnitCharacterChartCompatibility hj (Fo.K β).lev (c.embW u w h) (Lc.ψ β)

  chRat : ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

  hypC : ∀ β, HypTJC (Lc.t β)

  ok : Fo.okW w

  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T

  Lb_eq : ∀ β, (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) (Lc.Lb β)

variable {hj} {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}
  {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X0 u w h Lv j Fo.Ch}

theorem StepTies.chi (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) (κ : (Fo.K β).lev.U) :
    ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ) :=
  chiUnit_of hj (Fo.K β).lev (S.sameU β) (c.embW u w h) (S.psi β) S.bad_p (fun x => c.embW_int u w h x) κ



theorem StepTies.ties (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LocTiesR hj Fo Lc (c.embW u w h) β :=
  { frRat := S.frRat β
    sameU := S.sameU β
    hypT := S.hypT β
    bad_p := S.bad_p
    std := S.std
    psi := S.psi β
    chiRat := fun κ => let ⟨r, _, _, hr⟩ := S.chi β κ; ⟨r, hr⟩
    chRat := S.chRat β }

theorem StepTies.lat (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LatTies hj w Fo β (Lc.Lb β) :=
  { siteGood_prime_torsion := S.siteGood_prime_torsion
    Lb_eq := S.Lb_eq β
    lat := fun cl => isLattice_chart (Fo.K β) cl
    chi := S.chi β }

theorem StepTies.core (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).Core (c.embW u w h) β :=
  core_of_R hj K ht hF (S.ties β)

theorem StepTies.valIntN (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).ValIntN (c.embW u w h) w := by
  have ties (β : Fo.Ch) : LocTies hj Fo Lc (Gt.gat_pos u w h) (c.embW u w h) β :=
    { frRat := S.frRat β
      sameU := S.sameU β
      hypT := S.hypT β
      bad_p := S.bad_p
      std := S.std
      pos_emb := fun v s x => locJ_pos_emb hj (Lc.t β) Lc.B K v s x
      wt := StepIn.wt_of (M := M) Gt w h Lv ht hF j hj (stepInOf hj Fo Lc (Gt.gat_pos u w h)) rfl β
      psi := S.psi β
      chiRat := (S.ties β).chiRat
      chRat := S.chRat β }
  exact valIntN_rec hj (c.embW u w h) ties Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    ((D.gat u w h).P.setting (plc Gt u w h)).frac_O (fun x => c.embW_int u w h x) S.lat

theorem StepTies.twUnit (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).TwUnit w β := by
  have lat : LatIn (stepInOf hj Fo Lc (Gt.gat_pos u w h)) w β :=
    { prime := h.1
      resChar := rfl
      siteGood_prime_torsion := S.siteGood_prime_torsion
      alg := fun v a => (X0.g u w h).spl_alg _ ((X0.g u w h).pl v).2 a
      base := fun v t =>
        Formalism.L2.G.RelativeIndexFlags.frlat_re (rankN D (j + 1) hj) ((X0.g u w h).pl v).1
          ((X0.g u w h).spl _ ((X0.g u w h).pl v).2) (Lc.Lb β) Lc.B
          ((Lc.t β).fr _ ((X0.g u w h).pl v).2) (S.frRat β _ _) ((Lc.t β).fr_lat _ ((X0.g u w h).pl v).2)
          (Fo.K β).lev.Lb (S.Lb_eq β) t
      lat := (S.lat β).lat
      chi := S.chi β }
  exact twUnit_of (stepInOf hj Fo Lc (Gt.gat_pos u w h)) (c.embW u w h) w β (S.core K ht hF β)
    (fun x => c.embW_int u w h x) lat

theorem StepTies.chX (S : StepTies hj Fo Lc Gt c) : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
  have charts : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) := by
    refine { hypC := ?_, inj := ?_, onto := ?_, cinj := ?_ }
    all_goals
      intro β
      let : Fintype (Lc.cmpt β) := Lc.fin β
    · exact locHypC_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) (S.frRat β) (S.hypC β)
    · exact fun a => gamI_inj_locJ hj (Lc.t β) Lc.B a
    · exact fun a => gamOnto_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β) a
    · exact compInj_locJ hj (Lc.t β) Lc.B (Fo.K β).lev (S.sameU β)
  exact charts

end Step

structure HypTiesI (X0 : Formalism.L2.Herm.Herm0 D) (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where

  fl_t : Fl.t = D.R.t

  fill : FillTie Gt u w h Fl

  step : ∀ j hj, ∃ (Fo : FormsIn (I.at' j hj).M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch),
    (I.at' j hj).st = stepInOf hj Fo Lc (Gt.gat_pos u w h) ∧ StepTies hj Fo Lc Gt c

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem HypTiesI.chX {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (I.at' j hj).st := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.chX

theorem HypTiesI.core {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    ∀ β, (I.at' j hj).st.Core (c.embW u w h) β := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.core K A.fl_t A.fill

theorem HypTiesI.fin {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    (gatJ Lv (j + 1)).FinClasses :=
  finClasses_of (S := (I.at' j hj).st) (A.core K j hj) (A.chX j hj)

theorem HypTiesI.hyp {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c I :=
  cmpJHyp_of_two c Gt Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    (A.core K)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.ok)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.twUnit K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.valIntN K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact iwF_of hj Fo Lc (Gt.gat_pos u w h))
    (A.fin K) A.chX
    (fun j hj => formsOnClassOf _)
    (fun j hj => Formalism.MainNotions.G.CmpJ.PEvValChain.cmpLiftOf_holds _ _)

structure HypTies (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  step : ∀ j hj, StepTies hj (Z.Fo j hj) (Z.Lc j hj) Gt c

theorem HypTies.toI {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) : HypTiesI X0 (Z.I Gt) Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    step := fun j hj => ⟨Z.Fo j hj, Z.Lc j hj, rfl, A.step j hj⟩ }

theorem HypTies.hyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c (Z.I Gt) := A.toI.hyp K

theorem HypTies.atHyp {Z : AtIn X0 Tw u μ w h Lv} (A : HypTies Z Gt c) (K : CmpTied D X0 T Gt c) : AtHyp Z Gt c :=
  { fl_t := A.fl_t
    fill := A.fill
    ties := fun j hj => (A.step j hj).ties
    hypC := fun j hj => (A.step j hj).hypC
    ok := fun j hj => (A.step j hj).ok
    twUnit := fun j hj => (A.step j hj).twUnit K A.fl_t A.fill
    valIntN := fun j hj => (A.step j hj).valIntN K A.fl_t A.fill
    fin := A.toI.fin K
    card := (A.hyp K).card }

section Fam

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}

end Fam

end Formalism.MainNotions.G.ChF

end
end
end
