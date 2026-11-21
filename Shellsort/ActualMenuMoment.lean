import Shellsort.HarvestTenSchedule

/-! Finite moments of the actual independent third-gap draw, conditional
on any fixed entrance permutation. The menu is identical at every moment order. -/
noncomputable section
namespace Shellsort.ActualMenuMoment
open Finset Actual214 RoughGapScaleAssembly HarvestAggregateBudget HarvestScaleNumbers
open HarvestBlockIteration
open HarvestMenuBlock
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def unitPow (r : ℕ) : ℝ := (2:ℝ)^(16*r)
private def cutoff (r : ℕ) : ℕ := 2^(128+32*r)
private def depth (r : ℕ) : ℕ := 512+128*r

private theorem unit_ge (r : ℕ) : (r:ℝ)+1 ≤ unitPow r := by
  induction r with
  | zero => norm_num [unitPow]
  | succ r ih =>
    unfold unitPow at *
    rw [Nat.mul_succ,pow_add]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) r]

private theorem cutoff_eq (r : ℕ) :
    (cutoff r : ℝ) = 2^128 * unitPow r ^ 2 := by
  unfold cutoff unitPow
  push_cast
  rw [←pow_mul,←pow_add]
  congr 1; omega

private theorem depth_exp (r : ℕ) :
    (2:ℝ)^(depth r) = 2^512 * unitPow r ^ 8 := by
  unfold depth unitPow
  rw [←pow_mul,←pow_add]
  congr 1; omega

private theorem moment_coefficients (r c g : ℕ) (hg : g ≤ 9*c) :
    2*18800*(g:ℝ)*cutoff r + highFoot c (cutoff r) (depth r)
        ≤ (2^150 * unitPow r ^ 2) * (c:ℝ) ∧
    bQ (cutoff r) (depth r) ≤ 1 / (2^34 * unitPow r) := by
  let u := unitPow r
  have ur : (r:ℝ)+1 ≤ u := unit_ge r
  have u1 : 1 ≤ u := by linarith [Nat.cast_nonneg (α:=ℝ) r]
  have up : 0 < u := by linarith
  have u2 : u ≤ u^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr u1) up.le]
  have factor : ((2*depth r-1:ℕ):ℝ) ≤ 1024*u := by
    have hh : ((2*depth r-1:ℕ):ℝ) ≤ (2*(512+128*r):ℕ) := by
      exact_mod_cast Nat.sub_le (2*depth r) 1
    push_cast at hh
    linarith [Nat.cast_nonneg (α:=ℝ) r]
  have dt : (cutoff r:ℝ) = 2^128*u^2 := cutoff_eq r
  have dp : 0 < (cutoff r:ℝ) := by rw [dt]; positivity
  have done : 1 ≤ (cutoff r:ℝ) := by rw [dt]; nlinarith
  have smallPi : 8*Real.pi/(cutoff r:ℝ) ≤ 32 :=
    (div_le_iff₀ dp).mpr (by linarith [Real.pi_lt_four])
  constructor
  · have g9 : (g:ℝ) ≤ 9*(c:ℝ) := by exact_mod_cast hg
    unfold highFoot
    calc
      _ ≤ 2*18800*(9*(c:ℝ))*(cutoff r:ℝ) +
          (c:ℝ)*((1024*u)*18800*(32+32)+4) := by gcongr
      _ ≤ _ := by
        rw [dt]
        calc
          _ = ((2*18800*9*2^128)*u^2 + (1024*u)*18800*(32+32)+4)*c := by ring
          _ ≤ _ := by gcongr; nlinarith
  · unfold bQ
    have q1 : ((2*depth r-1:ℕ):ℝ)*18800*(8*Real.pi/(cutoff r:ℝ))
        ≤ 1/(2^35*u) := by
      calc
        _ ≤ (1024*u)*18800*(32/(cutoff r:ℝ)) := by
          gcongr; linarith [Real.pi_lt_four]
        _ ≤ _ := by
          rw [dt]
          field_simp
          nlinarith [sq_pos_of_pos up]
    have q2 : 4*(2+(cutoff r:ℝ)^2)/(2:ℝ)^(depth r) ≤ 1/(2^35*u) := by
      rw [dt,depth_exp]
      change 4*(2+(2^128*u^2)^2)/(2^512*u^8) ≤ 1/(2^35*u)
      have h4 : 1 ≤ u^4 := one_le_pow₀ u1
      have h7 : u^4 ≤ u^7 := pow_le_pow_right₀ u1 (by decide)
      field_simp
      calc
        4*(1+2^255*u^4) ≤ 4*(u^7+2^255*u^7) := by gcongr; exact h4.trans h7
        _ = (4*(1+(2:ℝ)^255))*u^7 := by ring
        _ ≤ (2:ℝ)^476*u^7 := by
          gcongr
          calc
            _ ≤ (2:ℝ)^258 := by rw [show 258=255+3 by decide,pow_add]; norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by decide)
    apply (add_le_add q1 q2).trans
    change 1/(2^35*u) + 1/(2^35*u) ≤ 1/(2^34*u)
    field_simp
    nlinarith

def rms {n : ℕ} (p : RankPlacement n) : ℝ :=
  Real.sqrt (RoughGapSelection.energy p)

private theorem energy_nonneg {n : ℕ} (p : RankPlacement n) :
    0 ≤ RoughGapSelection.energy p := by
  have hp : 0 ≤ (squareDisplacement p : ℝ) := by
    exact_mod_cast (show 0 ≤ squareDisplacement p by unfold squareDisplacement; positivity)
  exact div_nonneg hp (Nat.cast_nonneg _)

private theorem rms_sq {n : ℕ} (p : RankPlacement n) :
    rms p ^ 2 = (squareDisplacement p : ℝ) / n := Real.sq_sqrt (energy_nonneg p)

private theorem rms_after_le {n : ℕ} (p : RankPlacement n) (w : List ℕ) :
    rms (sortWord p w) ≤ rms p := by
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast word_square_le p w

/-- RMS at the actual exit, including the fixed suffix. -/
private def exitRms {n : ℕ} (s : Stage) (p : RankPlacement n) (h : ℕ) : ℝ :=
  rms (sortWord p (stageWord s h))

private theorem actual_raw_moment {n : ℕ} (hn : 0<n) (s : Stage) (hc : 9400 ≤ gap s.j)
    (r : ℕ) (p : RankPlacement n) :
    (∑ h ∈ choices s.j, (exitRms s p h)^(r+2)) / ((choices s.j).card:ℝ) ≤
      (1/(2^34*unitPow r))*(rms p)^(r+2) +
      (2^150*unitPow r^2)*(gap s.j:ℝ)*(rms p)^(r+1) := by
  let G := choices s.j
  have nn : (0:ℝ)<n := by exact_mod_cast hn
  have cp : 0 < G.card := by
    have q : gap s.j / 9400 ≤ G.card := actual_window_card s.j hc
    omega
  have cc : 0 < (G.card:ℝ) := by exact_mod_cast cp
  have oldQ : 0 ≤ (squareDisplacement p:ℝ) := by
    exact_mod_cast (show 0 ≤ squareDisplacement p by unfold squareDisplacement; positivity)
  have oldF : 0 ≤ footrule p := by unfold footrule transport; positivity
  have rpos : 0 ≤ rms p := Real.sqrt_nonneg _
  have massBound : footrule p / n ≤ rms p := by
    have hh := RoughGapSelection.mass_sq_le_energy hn p
    change (footrule p / n)^2 ≤ RoughGapSelection.energy p at hh
    rw [← Real.sqrt_sq (div_nonneg oldF nn.le)]
    exact Real.sqrt_le_sqrt hh
  have cf := moment_coefficients r _ _ (retained_ratio s.j hc)
  have blockB := actual_block_budget_linear (D:=cutoff r) (m:=depth r) s.j hc
    (by unfold cutoff; positivity) (by unfold depth; omega) p
  have one : (∑ h ∈ G, (squareDisplacement (block s.j h p):ℝ)) / (G.card:ℝ) ≤
      (2^150*unitPow r^2)*(gap s.j:ℝ)*footrule p +
      (1/(2^34*unitPow r))*(squareDisplacement p:ℝ) :=
    blockB.trans (add_le_add (mul_le_mul_of_nonneg_right cf.1 oldF)
      (mul_le_mul_of_nonneg_right cf.2 oldQ))
  have terms (h : ℕ) : exitRms s p h ^ 2 ≤ (squareDisplacement (block s.j h p):ℝ)/n := by
    rw [exitRms, rms_sq]
    simp only [stageWord, sortWord]
    exact div_le_div_of_nonneg_right (Int.cast_le.mpr (word_square_le (block s.j h p) s.suffix)) nn.le
  have entry := div_le_div_of_nonneg_right (sum_le_sum (s:=G) fun h _ => terms h) cc.le
  have two : (∑ h ∈ G, (exitRms s p h)^2) / (G.card:ℝ) ≤
      (2^150*unitPow r^2)*(gap s.j:ℝ)*(rms p) + (1/(2^34*unitPow r))*(rms p)^2 := by
    calc
      _ ≤ (∑ h ∈ G, (squareDisplacement (block s.j h p):ℝ)/n) / (G.card:ℝ) := entry
      _ = ((∑ h ∈ G, (squareDisplacement (block s.j h p):ℝ))/(G.card:ℝ))/n := by
        rw [←sum_div,div_right_comm]
      _ ≤ _ := by
        apply (div_le_div_of_nonneg_right one nn.le).trans
        rw [add_div,rms_sq,mul_div_assoc,mul_div_assoc (1/_)]
        gcongr
  have envelope (h : ℕ) : (exitRms s p h)^(r+2) ≤ (rms p)^r * (exitRms s p h)^2 := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (rms_after_le p (stageWord s h)) _) (sq_nonneg _)
  calc
    _ ≤ (∑ h ∈ G, (rms p)^r * (exitRms s p h)^2)/(G.card:ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum fun h _ => envelope h) cc.le
    _ = (rms p)^r * ((∑ h ∈ G, (exitRms s p h)^2)/(G.card:ℝ)) := by rw [←mul_sum]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left two (pow_nonneg rpos _)).trans_eq (by
      rw [pow_add,pow_succ]; ring)

/-- State conditional moment drift for the true menu and actual fixed
    suffix. The statement holds simultaneously for every integer order r+2. -/
theorem actual_stage_moment_drift {n H : ℕ} (hn : 0<n) (hH : 0<H)
    (s : Stage) (hc : 9400 ≤ gap s.j) (ratio : H ≤ 2^16*gap s.j)
    (r : ℕ) (p : RankPlacement n) :
    (∑ h ∈ choices s.j, (rms (sortWord p (stageWord s h)) / (gap s.j:ℝ))^(r+2)) /
      ((choices s.j).card:ℝ) ≤
      (1/4)*(rms p / (H:ℝ))^(r+2) +
      (2:ℝ)^(130*(r+2))*(rms p / (H:ℝ))^(r+1) := by
  let c : ℝ := gap s.j
  let R : ℝ := 2^16
  let y := rms p / (H:ℝ)
  have hp : (0:ℝ)<H := by exact_mod_cast hH
  have cp : 0<c := by dsimp [c]; exact_mod_cast (show 0<gap s.j by omega)
  have rr : (H:ℝ) ≤ R*c := by dsimp [R,c]; exact_mod_cast ratio
  have rp : 0 ≤ rms p := Real.sqrt_nonneg _
  have yy : 0 ≤ y := div_nonneg rp hp.le
  have grow : rms p/c ≤ R*y := by
    apply (div_le_iff₀ cp).mpr
    have h := mul_le_mul_of_nonneg_right rr yy
    have e : (H:ℝ)*y = rms p := by dsimp [y]; field_simp
    rw [e] at h
    linarith only [h, show R*c*y = R*y*c by ring]
  have exponent : R^r = unitPow r := by simp [R,unitPow,pow_mul]
  have up : 0 < unitPow r := by unfold unitPow; positivity
  have first : (1/(2^34*unitPow r))*R^(r+2) = 1/4 := by
    rw [pow_add,exponent]
    dsimp [R]
    field_simp
    ring
  have second : (2^150*unitPow r^2)*R^(r+1) ≤ (2:ℝ)^(130*(r+2)) := by
    rw [pow_succ R r,exponent]
    calc
      _ = (2:ℝ)^(150+16*r*3+16) := by
        simp only [unitPow,R,pow_add,pow_mul]
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have normed := div_le_div_of_nonneg_right (actual_raw_moment hn s hc r p)
    (pow_nonneg cp.le (r+2))
  change (∑ h ∈ choices s.j, (exitRms s p h / c)^(r+2)) / _ ≤ (1/4)*y^(r+2) + _*y^(r+1)
  calc
    _ = ((∑ h ∈ choices s.j, (exitRms s p h)^(r+2)) / ((choices s.j).card:ℝ))/c^(r+2) := by
      simp only [div_pow,←sum_div,div_right_comm (∑ h ∈ choices s.j, exitRms s p h ^ (r+2)) (c^_)]
    _ ≤ _ := normed.trans ?_
  change (_ + _*c*(rms p)^(r+1))/c^(r+2) ≤ _
  calc
    _ = (1/(2^34*unitPow r))*(rms p/c)^(r+2) + (2^150*unitPow r^2)*(rms p/c)^(r+1) := by
      rw [div_pow,div_pow,show r+2 = (r+1)+1 by omega,pow_succ c]
      field_simp
    _ ≤ (1/(2^34*unitPow r))*(R*y)^(r+2) + (2^150*unitPow r^2)*(R*y)^(r+1) := by
      gcongr
    _ ≤ _ := by
      rw [mul_pow,mul_pow,←mul_assoc,←mul_assoc,first]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right second (pow_nonneg yy _))

#print axioms actual_stage_moment_drift

/-- Conditional expectation over fresh uniform choices in successive stages. -/
def terminalMoment {n : ℕ} (r : ℕ) (H : ℕ) (p : RankPlacement n) :
    List Stage → ℝ
  | [] => (rms p/H)^(r+2)
  | s::ss => (∑ h ∈ choices s.j,
      terminalMoment r (gap s.j) (sortWord p (stageWord s h)) ss) /
      ((choices s.j).card:ℝ)

private theorem absorb (r : ℕ) (x K : ℝ) (hx : 0≤x) (hk : 0≤K) :
    (1/4)*x^(r+2)+K*x^(r+1) ≤ (1/2)*x^(r+2)+(1/2)*(4*K)^(r+2) := by
  have split (t : ℝ) : t^(r+2) = t*t^(r+1) := by
    rw [show r+2 = (r+1)+1 by omega,pow_succ]; ring
  by_cases h : 4*K ≤ x
  · have h' := mul_le_mul_of_nonneg_right h (pow_nonneg hx (r+1))
    have h'' := pow_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hk) (r+2)
    rw [split x]
    linarith
  · have h' := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx (le_of_not_ge h) (r+1)) hk
    have e := pow_nonneg hx (r+2)
    have f := pow_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hk) (r+2)
    rw [split (4*K)] at f ⊢
    linarith

/-- True product-menu expectation, with a geometric term for the incoming
    state. The number of stages is unrestricted as long as their scales fit. -/
theorem terminal_moment_bound {n H : ℕ} (hn : 0<n) (hp : 0<H)
    (ss : List Stage) (fit : Centers H ss) (p : RankPlacement n) (r : ℕ) :
    terminalMoment r H p ss ≤
      (1/2:ℝ)^ss.length*(rms p/H)^(r+2) +
      (1-(1/2:ℝ)^ss.length)*(4*(2:ℝ)^(130*(r+2)))^(r+2) := by
  induction ss generalizing H p with
  | nil => simp [terminalMoment]
  | cons s ss ih =>
    obtain ⟨hc,ratio,tail⟩ := fit
    have gp : 0<gap s.j := by omega
    let G := choices s.j
    have cp : 0<G.card := by
      have q : gap s.j / 9400 ≤ G.card := actual_window_card s.j hc
      omega
    have cc : (0:ℝ)<G.card := by exact_mod_cast cp
    let a : ℝ := (1/2:ℝ)^ss.length
    let K : ℝ := (2:ℝ)^(130*(r+2))
    let L := (4*K)^(r+2)
    let z := rms p / (H:ℝ)
    let f := fun h => (rms (sortWord p (stageWord s h))/(gap s.j:ℝ))^(r+2)
    let g := fun h => terminalMoment r (gap s.j) (sortWord p (stageWord s h)) ss
    have each (h : ℕ) : g h ≤ a*f h+(1-a)*L := ih gp tail _
    have bound : (∑ h ∈ G, f h)/(G.card:ℝ) ≤ (1/2)*z^(r+2)+(1/2)*L :=
      (actual_stage_moment_drift hn hp s hc ratio r p).trans
        (absorb r z K (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) (by dsimp [K]; positivity))
    have apos : 0≤a := by dsimp [a]; positivity
    change (∑ h ∈ G, g h)/(G.card:ℝ) ≤ _
    calc
      _ ≤ (∑ h ∈ G, (a*f h+(1-a)*L))/(G.card:ℝ) :=
        div_le_div_of_nonneg_right (sum_le_sum fun h _ => each h) cc.le
      _ = a*((∑ h ∈ G, f h)/(G.card:ℝ))+(1-a)*L := by
        simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
        field_simp
      _ ≤ a*((1/2)*z^(r+2)+(1/2)*L)+(1-a)*L :=
        add_le_add (mul_le_mul_of_nonneg_left bound apos) le_rfl
      _ = _ := by
        simp only [List.length_cons,pow_succ (1/2:ℝ)]
        change a*((1/2)*z^(r+2)+(1/2)*L)+(1-a)*L = (a*(1/2))*z^(r+2)+(1-a*(1/2))*L
        ring

#print axioms terminal_moment_bound

private theorem centers_take {H : ℕ} {ss : List Stage} (fit : Centers H ss) (k : ℕ) :
    Centers H (ss.take k) := by
  induction k generalizing H ss with
  | zero => simp [Centers]
  | succ k ih =>
    cases ss with
    | nil => trivial
    | cons s ss => exact ⟨fit.1,fit.2.1,ih fit.2.2⟩

/-- On the actual size-indexed menu, at the end of *any prefix of completed
    stages*, each fixed input has an order-uniform moment envelope. -/
theorem actual_prefix_moment {n : ℕ} (hn : 2 ≤ n) (p : RankPlacement n) (r k : ℕ) :
    terminalMoment r n p ((HarvestTenSchedule.stages (HarvestTenSchedule.count n)).take k) ≤
      (4*(2:ℝ)^(130*(r+2)))^(r+2) := by
  let ss := (HarvestTenSchedule.stages (HarvestTenSchedule.count n)).take k
  have hp : 0<n := by omega
  have nn : (0:ℝ)<n := by exact_mod_cast hp
  have fit : Centers n ss := centers_take (HarvestTenSchedule.centers_from_size hn) k
  have en := initial_bound hp (fun _ => p)
  simp only [meanEnergy, uniformAverage_const, scaleBound] at en
  have rt := (Real.sqrt_le_sqrt en).trans_eq (Real.sqrt_sq (by positivity))
  have ini : rms p/(n:ℝ) ≤ (2:ℝ)^115 := (div_le_iff₀ nn).mpr rt
  have large : (2:ℝ)^115 ≤ 4*(2:ℝ)^(130*(r+2)) := by
    calc
      _ ≤ (2:ℝ)^(130*(r+2)) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by norm_num)
  have cap := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) nn.le) (ini.trans large) (r+2)
  apply (terminal_moment_bound hp hp ss fit p r).trans
  have weighted := mul_le_mul_of_nonneg_left cap
    (pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) ss.length)
  let a := (1/2:ℝ)^ss.length
  let V := (4*(2:ℝ)^(130*(r+2)))^(r+2)
  calc
    _ ≤ a*V+(1-a)*V := add_le_add weighted le_rfl
    _ = V := by ring

#print axioms actual_prefix_moment
end Shellsort.ActualMenuMoment
