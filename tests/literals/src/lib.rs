fn test() {
    let should_work = if true { 1 + 2 } else { 3 + 4 };
    // let should_work = if true {
    //     let x = 9;
    //     x + 2;
    // } else {
    //     3 + 4
    // };

    // let should_work = match (1, 2) {
    //     _ => {
    //         let x = 9;
    //         let y = if true {
    //             let x = 10;
    //             0
    //         } else {
    //             9
    //         };
    //         x + y
    //     }
    // };

    // let should_fail = 1 + {
    //     let x = 9;
    //     x
    // };
    let should_fail = 1 + (if true { 9 } else { 10 });
}
