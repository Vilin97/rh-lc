module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColRecCEvBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColMatchAll

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem colMatchAll : ColMatchAll := by
  intro B X I h hX l Z hJ u a
  have KO := GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a
  refine ⟨?_, fun c x φ F z hx hF => ?_⟩
  · obtain ⟨⟨b⟩, hb⟩ := KO.period
    obtain ⟨hY, hK, hF, -, -⟩ := hb b
    exact ⟨⟨b, hY, hK, hF⟩⟩
  · obtain ⟨hY, hK, hF', hM, heq⟩ := KO.period.2 c.b
    have ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ := Subtype.ext (funext hx)
    have eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z := by
      apply Subtype.ext; funext t p; exact hF p
    subst ex; subst eF
    rw [heq φ z]
    rfl

end GlobalTheory.Core.Ht2

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NrmStepZeroEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChKerCCongr

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

section Congr

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {A A' : Amb X} (hA : ∀ (a b : ℕ) T (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) c x,
    IsSdLat N → IsSdLat N' → A.jetK T N N' c x = A'.jetK T N N' c x)


include hA in
theorem kerOf_congr (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) (T cA cB) {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') (fr fr' Ξ) :
    kerOf (stepC W Ch sel mu cst A u i lam') T cA cB N fr N' fr' Ξ = kerOf (stepC W Ch sel mu cst A' u i lam') T cA cB N fr N' fr' Ξ := by
  unfold kerOf stepC thDistC
  simp only [hA _ _ _ _ _ _ _ hN hN']


include hA in
theorem chKerC_congr (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) (h' : KerEquivC W Ch sel mu cst L A' u m2 b hY P) :
    chKerC W Ch sel mu cst L A u m2 b hY P h = chKerC W Ch sel mu cst L A' u m2 b hY P h' := by
  classical
  have e1 : matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = matK W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext i al be p p'
    exact kerOf_congr W Ch sel mu cst hA u i _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _
  have e2 : cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext al p p' Y
    unfold cp1K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u m2 _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _) rfl
  have e3 : cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) = cp2K W Ch sel mu cst (chTh W Ch sel mu cst A' u m2) := by
    funext p Y d
    unfold cp2K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u (m2 + 1) _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩
        ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _ _ _) rfl
  unfold chKerC chKer
  congr 1
  · funext i al be
    split_ifs
    · congr 1
      rw [e1]
    · rfl
  · funext al
    congr 1
    rw [e2]

end Congr

section True

open GlobalTheory.Core.Ht2 GlobalTheory.Mem.Col2.KerRat

variable {B : Base} {X : PreX B.toPre} {I : TC B X} (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
  (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (hX : B.fields.Ok)


include hχ in
theorem jetK_chi (a b : ℕ) (T) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E a)) (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E b)) (c x)
    (hN : IsSdLat N) (hN' : IsSdLat N') : (I.J.amb B χ).jetK T N N' c x = I.A.jetK T N N' c x := by
  have hf : Th.chiFac B.host χ a b N N' = Th.chiFac B.host I.chi a b N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (RcHyp.n1_detStd I l Z hN),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (RcHyp.n1_detStd I l Z hN')]
  have e3 : (I.J.amb B χ).e a b N N' = I.A.e a b N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd T N N' c x = I.A.thInd T N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  funext m
  unfold Amb.jetK
  rw [e4, show (I.J.amb B χ).chiF a b N N' = I.A.chiF a b N N' from hf]
  rfl


include hp ht hJ hχ in
theorem exists_cpl (u : B.Word) (a : I.ι) (cst : LocCst B.fields (rowSG (B.primes X) I.sel (I.tup a)))
    (L : ChIdx B.fields (B.primes X) B.R (I.Q a)) (e1 : cst = I.cst a) (e2 : L = I.idx a) (b : L.β (B.R.m - 2 + 1))
    (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) cst L u (B.R.m - 2) b)
    (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) L u j).Ok) (hL : L.Ok I.Ch I.sel (I.tup a) cst I.glob (B.R.m - 2)) :
    ∃ c : CplData I u a, ∀ (φ : ColsK I u) (z : RowsK I a),
      PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u
        (colC (chKerC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps hK) hF hL φ).1 z.1 =
        c.per h hX φ z := by
  subst e1 e2
  have hK' := (RcHyp.hyps_of_isTw I h hp l Z ht hJ I.chi (fun _ _ => rfl) a u).2.2.2 b hY
  refine ⟨⟨b, hY, hK', hF⟩, fun φ z => ?_⟩
  rw [chKerC_congr (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (jetK_chi l Z χ hχ) u _ b hY I.Ps hK hK']
  rfl

theorem exists_eNu (l0 : I.Law0 l) (u : B.Word) :
    ∃ e : (Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL) ≃ₗ[B.LL] (Z.V.div.Nu u).V,
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt (Z.V.div.Nu u).b (Z.V.div.Nu u).X v (e x) (e y) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL _) (MramH (Pr := B.primes X) B.wts I.Ch hX u).X v x y) ∧
      ∀ x, Z.V.nuIn u (e x) = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := by
  obtain ⟨eM, hs, -, hn, -⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  let eL : (Z.V.div.Nu u).V ≃ₗ[B.LL] MramV (Pr := B.primes X) B.wts I.Ch u := { eM with map_smul' := hs }
  let bs := ramBas (Pr := B.primes X) B.wts I.Ch hX u
  have hin : ∀ x, Z.V.nuIn u ((bs.equivFun.symm.trans eL.symm) x) =
      colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := fun x =>
    (hn _).trans (congrArg (fun φ : MramV (Pr := B.primes X) B.wts I.Ch u => colForm I l h u I.mu0 φ.1) (eL.apply_symm_apply _))
  refine ⟨bs.equivFun.symm.trans eL.symm, fun v x y => ?_, hin⟩
  haveI : IsTotallyComplex B.LL := hX.cplxK
  refine GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ v (bs.equivFun.symm.trans eL.symm).toLinearMap (fun x => congrArg (· ^ 2) ?_) x y
  refine (Z.V.nuIn_norm u v _).trans ?_
  rw [LinearEquiv.coe_coe, hin]
  refine (GlobalTheory.Core.ColNorm.nrm_stepZero_eq I h hX l u I.mu0 _ (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) (fun _ => rfl) v).trans ?_
  refine (ramInclH_norm (Pr := B.primes X) B.wts I.Ch hX u v (bs.equivFun.symm x)).symm.trans ?_
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 2
  funext i
  exact congrArg v.embedding (congrFun (bs.equivFun.apply_symm_apply x) i)


include hJ in
theorem perCol_eq (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (u : B.Word) (a : I.ι) (c : CplData I u a) (n : (Z.V.div.Nu u).V) (φ : ColsK I u) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 φ)
    (z : RowsK I a) : Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) = B.embLL (c.per h hX φ z) := by
  obtain ⟨-, -, -, -, hT⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  have hM := (colMatchAll I h hX l Z hJ u a).2 c (colForm I l h u a φ) φ
  have hj := (Z.V.nuIn_jN u n).trans (congrArg ((I.fm l u I.mu0).emb 0) hn)
  by_cases ha : a = I.mu0
  · subst ha
    refine (Z.W.perCol_base_eq_PtilCol u _ _).trans ?_
    rw [hj]
    exact hM _ z (fun _ => rfl) fun p => h0 u _ p
  · refine (Z.W.perCol_tie u a ha _ _).trans ?_
    rw [hj, ← hT a φ]
    exact hM _ z (fun _ => rfl) fun p => h1 u a _ p



theorem face_pt (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
    (Zs : DefSub (famC I hX U Xg tr).fam3.amb3) (u : B.Word) (a : I.ι) (ha) (x : Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL)
    (n : (Z.V.div.Nu u).V) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x))
    (f : Fin (((famC I hX U Xg tr).side3 (lev1 I) (chr1 I) Zs).nV ⟨I.tup a, ha⟩) → B.LL) (z : RowsK I a)
    (hz : z.1 = ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).ev Zs ⟨I.tup a, ha⟩ f).1.1) :
    B.embLL (((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).face Zs).Pt u ⟨I.tup a, ha⟩ x f) =
      Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) := by
  obtain ⟨c, hc⟩ := exists_cpl h hp l Z ht hJ χ hχ hX u a _ _ (cstT_tup ht a) (idxT_tup ht a)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).b ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hY ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hK ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hF ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hL ⟨I.tup a, ha⟩)
  rw [perCol_eq h l Z hJ hX l0 e h0 h1 u a c n _ hn z, ← hc, hz]
  rfl

end True

end GlobalTheory.Mem.R3.SelC

end
end
end
