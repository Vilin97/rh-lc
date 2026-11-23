module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLeWidth
public import Formalism.SharpRestriction.ParConsts
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LocalBoundElevenComparison

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoRGLeKOfSize

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem two_rG_le_k_of_size {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} (hS : Formalism.MainNotions.SizesAt L)
    (h : 70 < L.sc.x * L.sc.eps) : 2 * Formalism.MainNotions.G.rG L.sc ≤ D.R.k := by
  by_contra hk
  have hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc := not_le.1 hk
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk.le
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 he.le
  have h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps =
      2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps) := by
    field_simp
  rw [h7] at h6
  unfold Formalism.MainNotions.G.hG at h6
  linarith

theorem two_rG_le_k_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 2 * rG (Fm.L x i).sc ≤ (Fm.D x i).R.k := by
  refine ⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩
  have hs : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hp : 0 < eps := he ▸ (Fm.L x i).sc.eps_pos
  rw [hs, he]
  have : 71 ≤ x * eps := (div_le_iff₀ hp).1 hx
  linarith

end GlobalTheory.TwU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeValuationBound

section

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

end GlobalTheory.Proof.LatticeValuationBound

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnWeightComparison

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.ColumnWeightComparison

theorem colGeTw_of_cmpLite {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} (Ch : Chain Lv) (h : CmpLite D c Tw u μ w hg Ch)
    (x : ((D.fm u).lat 0).V) (s : ℝ)
    (hx : vGeLat (D.gat u w hg) (Lv.Int D.R.m) (Ch.chainK D.R.m (c.cmp u w hg x)) s) :
    WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s := by
  obtain ⟨cmp, h0, hK, hrat, hval⟩ := h
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.Proof.LatticeValuationBound.exists_chain (Tw.fm u μ) Ch (c.embW u w hg) cmp hK hrat
    (Tw.e0 u μ x) D.R.m le_rfl
  refine ⟨y, ?_, hval y s (by rw [hy', h0]; exact hx)⟩
  rw [hy, Tw.embed_mul_block_embedding]
  rfl

theorem colGe0_of_colGeTw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) (h0 : Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : WeilJacquetShalikaLaw.ColGeTw Tw u D.what₂.mu0 w x s) : WeilJacquetShalikaLaw.ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(Tw.eMu0 u D.R.m le_rfl).symm y, ?_,
    GlobalTheory.Proof.LatticeValuationBound.VGe_symm _ _ _ (Tw.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := Tw.eMu0_emb u D.R.m le_rfl ((Tw.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  have h2 := Tw.eMu0_emb u 0 (Nat.zero_le _) x
  rw [← h0, Tw.embed_mul_block_embedding] at h2
  exact eq_of_heq (h1.symm.trans (GlobalTheory.Proof.LatticeValuationBound.col_heq (D.memberColumns_twistedChain_base u) h2))

theorem cmpV_of_cmpLite (D : D7) (Y : LatInst D) (c : LatCmp D) (Dx : DivX D) (Tw : TwForms D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv)
    (h0 : ∀ u, Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : ∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
      CmpLite D c Tw u μ w hg (LC μ u w hg).2) :
    WeilJacquetShalikaLaw.CmpV c Dx Tw (reW Y LC) := by
  intro u w hg μ hU hQ x s hx
  have key : WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s :=
    colGeTw_of_cmpLite c Tw u μ w hg (LC μ u w hg).2 (h μ hU u w hg hQ) x s hx
  refine ⟨?_, fun _ => key⟩
  rintro rfl
  exact colGe0_of_colGeTw Tw u w x s (h0 u) key

end GlobalTheory.Proof.ColumnWeightComparison
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.local_systems_lower_bounds_second_real_place : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  first | exact @GlobalTheory.TwU.SiteSys.sysTw_sites | exact GlobalTheory.TwU.SiteSys.sysTw_sites | (intros; apply GlobalTheory.TwU.SiteSys.sysTw_sites <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryWeightModels

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.UnitaryWeightModels

theorem rowTwU_of_models : OrbitPlaces.OrbitLetterBoundsAll 11 1 → ∀ {eps : ℝ} (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ E : OrbitPlaces.Ent (Fm.D x i),
      OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) E) →
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ModelsOK (Fm.D x i) (Fm.Gy x i) (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw) →
    RowTwU Fm := by
  rintro h01 eps Fm ⟨xa, ha⟩ ⟨xb, hb⟩
  have hCL : OrbitPlaces.CLarge 11 1 Fm.GK Fm.cX.err :=
    OrbitPlaces.cLarge_of_fixed Fm.fixed.2.2.2.2.1 Fm.fixed.2.2.2.2.2.1 Fm.fixed.2.1
      (by rw [Fm.fixed.2.2.1]; norm_num)
  refine ⟨max xa xb, fun x hx h1 i => ?_⟩
  obtain ⟨E, hS⟩ := ha x (le_trans (le_max_left _ _) hx) h1 i
  obtain ⟨h0, LC, hLC⟩ := hb x (le_trans (le_max_right _ _) hx) h1 i
  exact ⟨LC,
    GlobalTheory.Proof.ColumnWeightComparison.cmpV_of_cmpLite _ _ _ _ _ LC h0 fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).1,
    GlobalTheory.T.local_systems_lower_bounds_second_real_place _ _ (Fm.gatT x i) _ _ _ _ _ _ _ E LC (Fm.latTied x h1 i) (Fm.ex x h1 i).fills_all
      (Fm.ex x h1 i).fdef h01 hS hCL fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).2⟩

end GlobalTheory.Proof.UnitaryWeightModels
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

noncomputable def entStd (D : D7) : Formalism.MainNotions.OrbitPlaces.Ent D := ⟨nuD D, nuRowOK D, nuD_rows D, 0, 0, 0, 0⟩

theorem rowTwU : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ModelsAt D O) →
    Row Q Lk fun 𝒜 _ => Closed 𝒜 fun Fm _ => GlobalTheory.TwU.RowTwU Fm := by
  intro Bd Q Lk hE
  refine ⟨fun _ D O _ _ => ModelsAt D O, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ => ?_⟩⟩
  obtain ⟨_, _, _, t⟩ := s Fm hc
  have h01 : Formalism.MainNotions.OrbitPlaces.OrbitLetterBoundsAll 11 1 := Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights.split_bound_eleven_one
  obtain ⟨xa, ha⟩ := GlobalTheory.ShapeRows.shape Fm
  obtain ⟨xb, hb⟩ := GlobalTheory.TwU.two_rG_le_k_large Fm
  refine GlobalTheory.Proof.UnitaryWeightModels.rowTwU_of_models h01 Fm ⟨xa, fun x hx h1 i => ⟨entStd _, ha x hx h1 i _⟩⟩
    ⟨xb, fun x hx h1 i => (t x h1 i).2 (Fm.latTied x h1 i) (hb x hx h1 i)⟩

end GlobalTheory.Svd
end
end
