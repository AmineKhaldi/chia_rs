use chia_protocol::Coin;
use rand::rngs::StdRng;
use rand::RngCore;
use rand::SeedableRng;
use std::collections::HashSet;

pub fn native_knapsack_coin_algorithm(
    smaller_coins: Vec<Coin>,
    target: u64,
    max_coin_amount: u64,
    max_num_coins: usize,
    seed: Option<Vec<u8>>,
) -> Option<HashSet<Coin>> {
    let mut seed = seed.unwrap_or_else(|| b"knapsack seed".to_vec());
    seed.resize(32, 0);
    let mut best_set_sum = max_coin_amount;
    let mut best_set_of_coins: Option<HashSet<Coin>> = None;
    let mut rng = StdRng::from_seed(seed.as_slice().try_into().unwrap());
    for _ in 0..1000 {
        let mut selected_coins: HashSet<Coin> = HashSet::new();
        let mut selected_coins_sum = 0;
        let mut target_reached = false;
        for n_pass in 0..2 {
            if target_reached {
                break;
            }
            for coin in &smaller_coins {
                if (n_pass != 0 || rng.next_u32() % 2 != 0)
                    && (n_pass != 1 || selected_coins.contains(coin))
                {
                    continue;
                }
                if selected_coins.len() > max_num_coins {
                    break;
                }
                selected_coins_sum += coin.amount;
                selected_coins.insert(coin.clone());
                if selected_coins_sum == target {
                    return Some(selected_coins);
                }
                if selected_coins_sum > target {
                    target_reached = true;
                    if selected_coins_sum < best_set_sum {
                        best_set_of_coins = Some(selected_coins.clone());
                        best_set_sum = selected_coins_sum;
                        // Remove the last added coin to try a different combination
                        selected_coins_sum -= coin.amount;
                        selected_coins.remove(coin);
                    }
                }
            }
        }
    }
    best_set_of_coins
}

#[cfg(test)]
mod tests {
    use super::*;
    use chia_protocol::Bytes32;
    #[test]
    fn test_knapsack_coin_selection() {
        let a_hash = Bytes32::from(
            &hex::decode("ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
                .unwrap(),
        );
        let tries = 100;
        let coins_to_append: u64 = 1000;
        let amounts: Vec<u64> = (1..coins_to_append).rev().collect();
        let coin_list: Vec<Coin> = amounts
            .iter()
            .map(|&a| Coin {
                parent_coin_info: a_hash,
                puzzle_hash: a_hash,
                amount: 100_000_000 * a,
            })
            .collect();
        for i in 0..tries {
            let knapsack = native_knapsack_coin_algorithm(
                coin_list.clone(),
                30_000_000_000_000,
                u64::MAX,
                999_999,
                Some(vec![i as u8]),
            );

            assert!(knapsack.is_some());
            let sum_amount: u64 = knapsack.unwrap().iter().map(|coin| coin.amount).sum();
            assert!(sum_amount >= 310000000);
        }
    }

    #[test]
    fn test_knapsack_coin_selection_2() {
        let a_hash = Bytes32::from(
            &hex::decode("ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
                .unwrap(),
        );
        let coin_amounts = vec![6, 20, 40, 80, 150, 160, 203, 202, 201, 320];
        let mut coin_list: Vec<Coin> = coin_amounts
            .iter()
            .map(|a| Coin {
                parent_coin_info: a_hash,
                puzzle_hash: a_hash,
                amount: *a as u64,
            })
            .collect();
        // Sort in descending order
        coin_list.sort_by(|a, b| b.amount.cmp(&a.amount));
        for i in 0..100 {
            let knapsack = native_knapsack_coin_algorithm(
                coin_list.clone(),
                265,
                u64::MAX,
                99999,
                Some(vec![i as u8]),
            );
            assert!(knapsack.is_some());
            let selected_sum: u64 = knapsack.unwrap().iter().map(|coin| coin.amount).sum();
            assert!(265 <= selected_sum && selected_sum <= 281);
        }
    }
}
