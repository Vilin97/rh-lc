module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
public import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountDef
public import Development.WeilBound.ThetaLifts.Reductions.JoinDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CountableCompactOpen
public import Development.WeilBound.ThetaLifts.CartanFactorisation.RealTrans
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
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
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CommuteConj
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

-- Source module: Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem inf_uniq2 (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {n d : ℕ} {Y : Spc F E n}
    {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s')
    (hH : PositivityTheory.ThKR.JoinAt B M o) {N N'}
    (h1 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N)
    (h2 : Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P ∧ P ≠ M.Pol B.ψ B.emb) N') : N = N' := by
  have H := hH N N' h1.1.1 h2.1.1
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1.1.1
  obtain ⟨b1, -, -, b4, b5⟩ := h2.1.1
  have st : ∀ i, ∀ f ∈ N ⊔ N', ∀ y, RInf B o i f y → y ∈ N ⊔ N' := fun i f hf y hy => by
    obtain ⟨A, hA⟩ := exists_linop hO hL hQ hp i
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hf
    rw [((hA ⟨u + w, add_mem (a1 hu) (b1 hw)⟩).2 y).1 hy,
      show (⟨u + w, add_mem (a1 hu) (b1 hw)⟩ : M.Pol B.ψ B.emb) = ⟨u, a1 hu⟩ + ⟨w, b1 hw⟩ from rfl, map_add]
    have x1 := ((hA ⟨u, a1 hu⟩).2 _).2 rfl
    have x2 := ((hA ⟨w, b1 hw⟩).2 _).2 rfl
    rcases i with γ | k
    exacts [Submodule.add_mem_sup (a4 γ γ.2 u hu _ x1) (b4 γ γ.2 w hw _ x2),
      Submodule.add_mem_sup (a5 k k.2 u hu _ x1) (b5 k k.2 w hw _ x2)]
  exact max_uniq ⟨sup_le a1 b1, fun γ hγ f hf y e => Submodule.mem_sup_left (a2 γ hγ f hf y e),
    fun k hk f hf y e => Submodule.mem_sup_left (a3 k hk f hf y e), fun γ hγ => st (.inl ⟨γ, hγ⟩), fun k hk => st (.inr ⟨k, hk⟩)⟩
    H h1 h2

theorem archimedean_matched_maps_compare (hH : PositivityTheory.ThKR.JoinTri) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    {R R₂ : RealMaps F a a'} {Rf : FinMaps F a a'} (m : IsMatched B G X om om' R Rf) (m₂ : IsMatched B G X om om' R₂ Rf) :
    ∃ (e : R.Pi →ₗ[ℂ] R₂.Pi) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ G.M.Pol B.ψ B.emb, e (R.p x) = R₂.p x) ∧
      ∀ x ∈ G.M'.Pol B.ψ B.emb, e (R.p' x) = c • R₂.p' x := by
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' n)
      (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have p1 : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV, m.triple.geo.hW, m.triple.geo.hM, m.triple.chars.heckeβ,
      hecke_div m.triple.chars.heckeβ m.triple.chars.heckeα, m.triple.chars.resβ,
      res_div m.triple.chars.resβ m.triple.chars.resα rfl, m.triple.weil⟩
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV', m.triple.geo.hW, m.triple.geo.hM', m.triple.chars.heckeα,
      hecke_div m.triple.chars.heckeα m.triple.chars.heckeβ, m.triple.chars.resα,
      res_div m.triple.chars.resα m.triple.chars.resβ (add_comm _ _), m.triple.weil'⟩
  choose A hA using exists_linop hO hL hQ p1
  choose A' hA' using exists_linop hO hL hQ p2
  haveI := m₂.real.nontriv
  have eqv : ∀ {R : RealMaps F a a'}, IsRealMaps B G om om' R → ∀ i (x : G.M.Pol B.ψ B.emb) (x' : G.M'.Pol B.ψ B.emb),
      R.p x = R.p' x' → R.p (A i x) = R.p' (A' i x') := fun h i x x' => by
    have x1 := ((hA i x).2 _).2 rfl
    have x2 := ((hA' i x').2 _).2 rfl
    rcases i with γ | k
    exacts [h.lie γ γ.2 x x.2 x' x'.2 _ _ x1 x2, h.cpt k k.2 x x.2 x' x'.2 _ _ x1 x2]
  exact schur_match _ _ R.p R.p' R₂.p R₂.p' m.real.quot.onto m.real.quot'.onto m₂.real.quot.onto m₂.real.quot'.onto
    (fun x hx => (ker_of_eq (inf_uniq2 hO hL hQ p1 (hH F E σ B a a' G X om om' m.triple).1
      (maxInfP hO hL hQ m).1 (maxInfP hO hL hQ m₂).1) x hx).1)
    (ker_of_eq (inf_uniq2 hO hL hQ p2 (hH F E σ B a a' G X om om' m.triple).2
      (maxInfP hO hL hQ m).2 (maxInfP hO hL hQ m₂).2))
    A (fun i x => A' i x) (fun i x => (hA i x).1) (fun i x => (hA' i x).1) (eqv m.real) (eqv m₂.real)
    (fun N hN => m.real.irred N
      (fun γ hγ f hf y e hp => by rw [((hA (.inl ⟨γ, hγ⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
      fun k hk f hf y e hp => by rw [((hA (.inr ⟨k, hk⟩) ⟨f, hf⟩).2 y).1 e]; exact hN _ ⟨f, hf⟩ hp)
    (hC F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1)

end PositivityTheory.ThKF

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolReOf2T

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq

    simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul']
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
end
end

-- Source module: Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxFinTOfPublished

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem PositivityTheory.HoweDualityUnitaryAlt.polRe_of2T : PositivityTheory.ThKR.JoinTri → PositivityTheory.HoweDualityUnitaryAlt.MaxFinT → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.PolCount → PositivityTheory.ThKF.CartanConj → PositivityTheory.ThKF.CartanMove → GlobalTheory.ThK.KCoinv → PositivityTheory.ThKF.ILeft → GlobalTheory.ThK.PolRe := GlobalTheory.CompanionTheory.ThetaK.polRe_of2T
end
end
