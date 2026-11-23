module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValuStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongAtOfNearSame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PenultimateChartLocalGroupMemNearLevelSetStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMidLevOfMem

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem nearAt_congr' {n : ℕ} {x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g g' : GL (Fin N) E}
    (h : GlobalTheory.TwU.NearAt P n x g) (hx : x = x') (hg : g = g') : GlobalTheory.TwU.NearAt P n x' g' := hx ▸ hg ▸ h

theorem nearAt_inv_int {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g h : GL (Fin N) E}
    (hx : GlobalTheory.TwU.NearAt P n x g) (hh : h = g⁻¹)
    (hint : ∀ a b, IntAt P ((h : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((h⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.NearAt P n x⁻¹ h := by
  subst hh
  unfold GlobalTheory.TwU.NearAt at *
  have := GlobalTheory.CplPt.congAt_conj n (GlobalTheory.LevFrame.congAt_inv F E N n P _ hn hx) hint
  convert this using 1
  rw [map_inv]
  group

end Gen

section Near

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

theorem prCat_last_le_int (hI : I.Ok) (P : SBof I a) :
    prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  have hL := hI.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  obtain ⟨b, -⟩ := hL.last_uniq
  have h := hL.int _ b P
  rw [hL.last_h] at h
  rw [e]
  exact h

theorem nearV_one (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV
  exact nearAt_congr' (GlobalTheory.TwU.nearAt_self (F := (I.rec7 l Z).host.F) _ _ 1) ((map_one _).trans (map_one _).symm) (map_one _).symm

theorem nearV_mul (P : SBof I a) {x y} {g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hy : NearV I l Z a v P y g') (hg' : g' ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P (x * y) (g * g') := by
  unfold NearV at *
  exact nearAt_congr' (GlobalTheory.CplPt.nearAt_mul_int _ hx hy (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hg'⟩))
    (map_mul _ _ _).symm (map_mul _ _ _).symm

theorem nearV_inv (P : SBof I a) (hD : 1 ≤ (I.cst a).D P) {x}
    {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hg : g⁻¹ ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P x⁻¹ g⁻¹ := by
  unfold NearV at *
  exact nearAt_congr' (nearAt_inv_int hD hx (map_inv _ _) (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g⁻¹, hg⟩))
    (map_inv _ _).symm rfl

theorem mem_of_midLev (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))} {z : B.fields.K}
    (h : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z) :
    g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).1 ⟨z, h⟩

theorem exists_midLev_of_mem (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (h : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1) :
    ∃ z, GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).2 h

end Near

theorem nearSet_closed : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), 1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v ∧
      (∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x * y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v) ∧
      ∀ x, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x⁻¹ ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hI l Z a v
  refine ⟨fun P _ => ?_, fun x y hx hy P hP => ?_, fun x hx P hP => ?_⟩
  · obtain ⟨z, hz⟩ := exists_midLev_of_mem I a P (one_mem _)
    exact ⟨1, z, hz, nearV_one I l Z a v P⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    obtain ⟨g', z', hgz', hyg'⟩ := hy P hP
    have hg := mem_of_midLev I a P hgz
    have hg' := mem_of_midLev I a P hgz'
    obtain ⟨z'', hz''⟩ := exists_midLev_of_mem I a P (mul_mem hg hg')
    exact ⟨g * g', z'', hz'', nearV_mul I l Z a v P hxg hyg' (prCat_last_le_int I a hI P hg')⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    have hgi := inv_mem (mem_of_midLev I a P hgz)
    obtain ⟨z', hz'⟩ := exists_midLev_of_mem I a P hgi
    exact ⟨g⁻¹, z', hz', nearV_inv I l Z a v P ((hI.idx_ok a).cst_ok.D_pos P) hxg (prCat_last_le_int I a hI P hgi)⟩

end GlobalTheory.Mem.Col2.QChi

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MidLevMulBeforeLast

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

theorem last_rep_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∃ b : (I.idx a).β (B.R.m - 1), ∀ P, (I.idx a).h (B.R.m - 1) b P = 1 := by
  have hL := hOk.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  rw [e]
  obtain ⟨b, -⟩ := hL.last_uniq
  exact ⟨b, hL.last_h b⟩

theorem prCat_last_le_GLint {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have h := (hOk.idx_ok a).int (B.R.m - 1) b P
  rwa [hb P] at h

theorem inv_mul_rearrange {G : Type*} [Group G] (A B C D : G) : (A * B)⁻¹ * (C * D) = (B⁻¹ * D) * (D⁻¹ * (A⁻¹ * C) * D) := by
  group

theorem nearAt_prod_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ex ey : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (rg rg' : GL (Fin N) E)
    (hx : GlobalTheory.TwU.CongAt P n (ex⁻¹ * GlobalTheory.TwU.ratA F rg)) (hy : GlobalTheory.TwU.CongAt P n (ey⁻¹ * GlobalTheory.TwU.ratA F rg'))
    (hint : ∀ a b, IntAt P ((rg' : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((rg'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.CongAt P n ((ex * ey)⁻¹ * GlobalTheory.TwU.ratA F (rg * rg')) := by
  rw [map_mul, inv_mul_rearrange]
  exact GlobalTheory.CplPt.congAt_mul _ hy (GlobalTheory.CplPt.congAt_conj _ hx hint)

theorem nearV_mul_pairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) (x y : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P y g' z' → GlobalTheory.Mem.Col2.QChi.NearV I l Z a v P (x * y) (g * g') := by
  intro B X I hOk l Z a v P x y g g' z z' hx hy
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
    (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g').1 ⟨z', hy.1⟩
  have hint := prCat_last_le_GLint I hOk a P hg'
  have hx2 := hx.2
  have hy2 := hy.2
  unfold NearV GlobalTheory.TwU.NearAt at hx2 hy2 ⊢
  have key := nearAt_prod_of_conj _ _ _ _ _ _ hx2 hy2 (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hint⟩)
  rw [map_mul (GlobalTheory.Mem.Col2.ChartLevel.emb v)]
  erw [map_mul (GlobalTheory.TwU.seamGL (sm I l Z)) g g']
  exact key

theorem chiInv_last_eq_char {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    ∃ φ : ↥(prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1) →* B.fields.Kˣ,
      ∀ r ∈ Loc.Cbe (Jat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1) 1,
      ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
      (∀ x, r (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) = Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) (g x)) →
      chiInv I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 r = φ ⟨g, hg⟩ := by
  have hL := hOk.idx_ok a
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have hint := prCat_last_le_GLint I hOk a P
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        GlobalTheory.TopStep.redGL _ P.1 ⟨g, hint hg⟩ ∈ ((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).H := fun g hg =>
      (hL.grpG _ b ⟨P.1, hP⟩ _).2 ⟨g, by rw [hb]; exact hg, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx⟩
    refine ⟨((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).lam.comp
      (MonoidHom.codRestrict ((GlobalTheory.TopStep.redGL _ P.1).comp (Subgroup.inclusion hint)) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrG (B.R.m - 1) b ⟨P.1, hP⟩ ⟨_, hH g hg⟩ g r (by rw [hb]; exact hr) hrx
      (fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx)
    rw [hb] at hc
    exact hc.symm
  · classical
    have hQ := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        (⟨g, hint hg⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1)) ∈ ((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).H := fun g hg => by
      rw [hL.grpQ _ b ⟨P.1, hQ⟩, hb]
      exact Subgroup.mem_subgroupOf.2 hg
    refine ⟨((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).lam.comp
      (MonoidHom.codRestrict (Subgroup.inclusion hint) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrQ (B.R.m - 1) b ⟨P.1, hQ⟩ ⟨⟨g, hint hg⟩, hH g hg⟩ r (by rw [hb]; exact hr) hrx
    rw [hb] at hc
    exact hc.symm

theorem midLev_mul_beforeLast : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g' z' → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 (g * g') (z * z') := by
  intro B X I hOk a P g g' z z' ⟨r, hr, hrx, hz⟩ ⟨r', hr', hrx', hz'⟩
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  have hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r, hr, hrx⟩
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r', hr', hrx'⟩
  have hrr : ∀ x, (r * r') (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) =
      Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) ((g * g') x) := fun x => by
    rw [LinearEquiv.mul_apply, hrx', hrx]
    rfl
  refine ⟨r * r', mul_mem hr hr', hrr, ?_⟩
  rw [hz, hz', hφ r hr g hg hrx, hφ r' hr' g' hg' hrx', hφ (r * r') (mul_mem hr hr') (g * g') (mul_mem hg hg') hrr,
    ← Units.val_mul, ← map_mul]
  rfl

theorem midLev_one_last : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 1 1 := by
  intro B X I hOk a P
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  refine ⟨1, one_mem _, fun x => rfl, ?_⟩
  rw [hφ 1 (one_mem _) 1 (one_mem _) (fun x => rfl)]
  exact (congrArg Units.val (map_one φ)).symm

theorem nearV_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV GlobalTheory.TwU.NearAt
  erw [map_one (GlobalTheory.TwU.seamGL (sm I l Z)), map_one, map_one, inv_one, one_mul]
  exact GlobalTheory.TwU.congAt_one _ _

open Classical in
theorem valV_factor {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (P : SBof I a) (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K)
    (hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) (hn : NearPair I l Z a v P x g z) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = z := by
  rw [dite_eq_left ⟨hP, g, z, hn⟩]
  exact GlobalTheory.Mem.Col2.QChi.nearPair_val_unique I hOk l Z a v P x _ g _ z (Exists.choose_spec (Exists.choose_spec (⟨hP, g, z, hn⟩ : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z).2)) hn

open Classical in
theorem valV_factor_off {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (P : SBof I a) (hP : ¬ IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = 1 :=
  dif_neg fun h => hP h.1

theorem valV_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), GlobalTheory.Mem.Col2.QChi.valV I l Z a v 1 = 1 ∧ ∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → GlobalTheory.Mem.Col2.QChi.valV I l Z a v (x * y) = GlobalTheory.Mem.Col2.QChi.valV I l Z a v x * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y := by
  intro B X I hOk l Z a v
  constructor
  · unfold valV
    rw [Finset.prod_eq_one, map_one]
    intro P _
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · exact valV_factor I hOk l Z a v 1 P 1 1 hP ⟨midLev_one_last I hOk a P, nearV_one_one I l Z a v P⟩
    · exact valV_factor_off I l Z a v 1 P hP
  · intro x y hx hy
    unfold valV
    rw [← map_mul, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · have hx' : ∃ g z, NearPair I l Z a v P x g z := hx P hP
      have hy' : ∃ g z, NearPair I l Z a v P y g z := hy P hP
      obtain ⟨g, z, hgz⟩ := hx'
      obtain ⟨g', z', hgz'⟩ := hy'
      have hxy : NearPair I l Z a v P (x * y) (g * g') (z * z') := ⟨midLev_mul_beforeLast I hOk a P g g' z z' hgz.1 hgz'.1, nearV_mul_pairs I hOk l Z a v P x y g g' z z' hgz hgz'⟩
      rw [valV_factor I hOk l Z a v (x * y) P _ _ hP hxy, valV_factor I hOk l Z a v x P _ _ hP hgz, valV_factor I hOk l Z a v y P _ _ hP hgz']
    · rw [valV_factor_off I l Z a v (x * y) P hP, valV_factor_off I l Z a v x P hP, valV_factor_off I l Z a v y P hP, mul_one]

end GlobalTheory.Mem.Col2.QChi

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterAllChartsFurtherPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi


open GlobalTheory.Mem.Col2.ChartLevel in
theorem chi_eq_prod_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 F))) (G : Q → Type) [∀ v, Group (G v)]
    (ψv : ∀ v : Q, G v →* ℂˣ) (κ : S.U) (z : ∀ v : Q, G v)
    (hoff : ∀ v, v ∉ Q → bc (prV (E := E) v) κ.1 = 1)
    (h : ∀ v : Q, S.chi (embU S v.1 (cmp S v.1 κ)) = ψv v (z v)) :
    S.chi κ = (∏ v : Q, (ψv v).comp (Pi.evalMonoidHom G v)) z := by
  rw [MonoidHom.finsetProd_apply, chi_eq_prod S Q κ (fun w _ hw => hoff w hw), ← Finset.prod_coe_sort Q]
  exact Finset.prod_congr rfl fun v _ => h v



theorem exists_locChi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∃ ψv : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) →* ℂˣ, ∀ β (x : (K β).lev.Uloc v) (w : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1 = x.1 → (K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) = ψv w := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv
  have hB := GlobalTheory.Mem.Col2.QChi.nearSet_closed I hOk l Z a v
  have hC := GlobalTheory.Mem.Col2.QChi.valV_mul I hOk l Z a v
  let G' : Subgroup (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
    { carrier := GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v
      one_mem' := hB.1
      mul_mem' := fun {x y} hx hy => hB.2.1 x y hx hy
      inv_mem' := fun {x} hx => hB.2.2 x hx }
  let G'' := G'.comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  have hle : (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ≤ G'' :=
    iSup_le fun β' => Subgroup.comap_mono fun x hx => GlobalTheory.T.penultimateChart_localGroup_mem_nearLevelSet I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hU hchi Lb0 hLb v hv β' ⟨x, hx⟩
  let f : G'' →* ℂ :=
    { toFun := fun w => GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1)
      map_one' := by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ 1) = 1
        rw [map_one]
        exact hC.1
      map_mul' := fun x y => by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (x.1 * y.1)) = _
        rw [map_mul]
        exact hC.2 _ _ x.2 y.2 }
  refine ⟨(f.toHomUnits)⁻¹.comp (Subgroup.inclusion hle), fun β x w hw => ?_⟩
  have hd := GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv β x
  show _ = (f.toHomUnits (Subgroup.inclusion hle w))⁻¹
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  show (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1) = 1
  exact (congrArg (fun y => (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y) hw).trans hd



theorem exists_chi_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb
  choose ψv hψv using fun (v : Q) => exists_locChi I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v.1 v.2
  refine ⟨∏ v : Q, (ψv v).comp (Pi.evalMonoidHom (fun v : Q => ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) v), ?_⟩
  intro β κ z hz hoff
  exact chi_eq_prod_eval (K β).lev Q _ ψv κ z hoff (fun v => hψv v β _ (z v) (hz v))

end GlobalTheory.Mem.Col2.QChi

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterAllChartsFurtherPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_character_allCharts_furtherPlaces : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  first | exact @GlobalTheory.Mem.Col2.QChi.exists_chi_further | exact GlobalTheory.Mem.Col2.QChi.exists_chi_further | (intros; apply GlobalTheory.Mem.Col2.QChi.exists_chi_further <;> assumption)
end
end
