// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

error ExceedsPriceImpactAllowance();

contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    //   constructor () internal { }

    function _msgSender() internal view returns (address) {
        return payable(msg.sender);
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(
            _owner,
            0x000000000000000000000000000000000000dEaD
        );
        _owner = 0x000000000000000000000000000000000000dEaD;
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
}

library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

interface IERC20 {
    function name() external view returns (string memory);

    function symbol() external view returns (string memory);

    function totalSupply() external view returns (uint256);

    function decimals() external view returns (uint256);

    function balanceOf(address account) external view returns (uint256);

    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);

    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IPancakeRouter01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB, uint256 liquidity);

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (uint256 amountToken, uint256 amountETH, uint256 liquidity);
}

interface IPancakeRouter02 is IPancakeRouter01 {
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

interface IUniswapV2Factory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(
        address tokenA,
        address tokenB
    ) external view returns (address pair);

    function allPairs(uint256) external view returns (address pair);

    function allPairsLength() external view returns (uint256);

    function createPair(
        address tokenA,
        address tokenB
    ) external returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;
}

contract BaseFatToken is IERC20, Ownable {

    struct CooldownAllowance {
        uint16 priceImpactAllowance;
        uint32 endTimestamp;
    }

    bool public currencyIsEth;

    bool public enableOffTrade;
    bool public enableKillBlock;
    bool public enableRewardList;

    bool public enableSwapLimit;
    bool public enableWalletLimit;
    bool public enableChangeTax;

    address public currency;
    address public fundAddress;

    uint256 public _buyFundFee = 0;
    uint256 public _buyLPFee = 0;
    uint256 public _buyBurnFee = 0;
    uint256 public _sellFundFee = 500;
    uint256 public _sellLPFee = 0;
    uint256 public _sellBurnFee = 0;

    uint256 public kb = 0;

    uint256 public maxBuyAmount;
    uint256 public maxWalletAmount;
    uint256 public maxSellAmount;
    uint256 public startTradeBlock;

    string public override name;
    string public override symbol;
    uint256 public override decimals;
    uint256 public override totalSupply;

    ///////////COOLDOWNS///////////
    /* 
    Set "k" to (reserve0 * reserve1) prior to adding initial liquidity and use correct decimals scaling
        e.g. reserve0 = BNB, reserve1 = address(this) <-- ShibElon 2.0
        Decimals = 18
        Add 10 BNB, 1,000,000,000,000 ShibElon 2.0
        k = (10e18 * 1,000,000,000,000e18) = 1e49
    */
    uint internal constant k = 1e47;
    uint internal constant SCALE = 1e18;
    uint internal constant denominator = 10000;    
    event CooldownEnabledUpdated (bool _enabled);
    bool public _cooldownEnabled = false;
    uint16 public priceImpactAllowedPercentage = 100; // 1% // Replace where called for lower gas cost if fixed value desired
    uint32 public cooldownLength = 1 days; // Set constant for lower read cost if fixed value desired
    mapping (address => CooldownAllowance) public _cooldown;
    ///////////COOLDOWNS///////////

    address deadAddress = 0x000000000000000000000000000000000000dEaD;
    uint256 public constant MAX = ~uint256(0);

    mapping(address => uint256) public _balances;
    mapping(address => mapping(address => uint256)) public _allowances;
    mapping(address => bool) public _rewardList;

    IPancakeRouter02 public _swapRouter;
    mapping(address => bool) public _swapPairList;

    mapping(address => bool) public _feeWhiteList;
    address public _mainPair;

    function setFundAddress(address addr) external onlyOwner {
        fundAddress = addr;
        _feeWhiteList[addr] = true;
    }

    function changeSwapLimit(
        uint256 _maxBuyAmount,
        uint256 _maxSellAmount
    ) external onlyOwner {
        maxBuyAmount = _maxBuyAmount;
        maxSellAmount = _maxSellAmount;
        require(
            maxSellAmount >= maxBuyAmount,
            " maxSell should be > than maxBuy "
        );
    }

    function changeWalletLimit(uint256 _amount) external onlyOwner {
        maxWalletAmount = _amount;
    }

    function launch() external onlyOwner {
        require(startTradeBlock == 0, "already started");
        startTradeBlock = block.number;
    }

    function disableSwapLimit() public onlyOwner {
        enableSwapLimit = false;
    }

    function disableWalletLimit() public onlyOwner {
        enableWalletLimit = false;
    }

    function disableChangeTax() public onlyOwner {
        enableChangeTax = false;
    }

    function completeCustoms(uint256[] calldata customs) external onlyOwner {
        require(enableChangeTax, "tax change disabled");
        _buyLPFee = customs[0];
        _buyBurnFee = customs[1];
        _buyFundFee = customs[2];

        _sellLPFee = customs[3];
        _sellBurnFee = customs[4];
        _sellFundFee = customs[5];

        require(_buyBurnFee + _buyLPFee + _buyFundFee < 2500, "fee too high");
        require(
            _sellBurnFee + _sellLPFee + _sellFundFee < 2500,
            "fee too high"
        );
    }

    function transfer(
        address recipient,
        uint256 amount
    ) external virtual override returns (bool) {}

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external virtual override returns (bool) {}

    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    function allowance(
        address owner,
        address spender
    ) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(
        address spender,
        uint256 amount
    ) public override returns (bool) {
        _approve(msg.sender, spender, amount);
        return true;
    }

    function _approve(address owner, address spender, uint256 amount) private {
        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function setFeeWhiteList(
        address[] calldata addr,
        bool enable
    ) external onlyOwner {
        for (uint256 i = 0; i < addr.length; i++) {
            _feeWhiteList[addr[i]] = enable;
        }
    }

    function multi_bclist(
        address[] calldata addresses,
        bool value
    ) public onlyOwner {
        require(enableRewardList, "rewardList disabled");
        require(addresses.length < 201);
        for (uint256 i; i < addresses.length; ++i) {
            _rewardList[addresses[i]] = value;
        }
    }
}

contract TokenDistributor {
    constructor(address token) {
        IERC20(token).approve(msg.sender, uint256(~uint256(0)));
    }
}

contract FatToken is BaseFatToken {
    bool private inSwap;

    TokenDistributor public _tokenDistributor;

    modifier lockTheSwap() {
        inSwap = true;
        _;
        inSwap = false;
    }

    constructor(
        string[] memory stringParams,
        address[] memory addressParams,
        uint256[] memory numberParams,
        bool[] memory boolParams
    ) {
        name = stringParams[0];
        symbol = stringParams[1];
        decimals = numberParams[0];
        totalSupply = numberParams[1];
        currency = addressParams[0];

        _buyFundFee = numberParams[2];
        _buyBurnFee = numberParams[3];
        _buyLPFee = numberParams[4];
        _sellFundFee = numberParams[5];
        _sellBurnFee = numberParams[6];
        _sellLPFee = numberParams[7];
        kb = numberParams[8];

        maxBuyAmount = numberParams[9];
        maxSellAmount = numberParams[10];

        maxWalletAmount = numberParams[11];
        require(
            maxSellAmount >= maxBuyAmount,
            " maxSell should be > than maxBuy "
        );
        airdropNumbs = numberParams[12];
        require(airdropNumbs <= 3, "airdropNumbs should be <= 3");

        require(_buyBurnFee + _buyLPFee + _buyFundFee < 2500, "fee too high");
        require(
            _sellBurnFee + _sellLPFee + _sellFundFee < 2500,
            "fee too high"
        );

        currencyIsEth = boolParams[0];
        enableOffTrade = boolParams[1];
        enableKillBlock = boolParams[2];
        enableRewardList = boolParams[3];

        enableSwapLimit = boolParams[4];
        enableWalletLimit = boolParams[5];
        enableChangeTax = boolParams[6];
        enableTransferFee = boolParams[7];
        if (enableTransferFee) {
            transferFee = _sellFundFee + _sellLPFee + _sellBurnFee;
        }

        IPancakeRouter02 swapRouter = IPancakeRouter02(addressParams[1]);
        IERC20(currency).approve(address(swapRouter), MAX);
        _swapRouter = swapRouter;
        _allowances[address(this)][address(swapRouter)] = MAX;
        IUniswapV2Factory swapFactory = IUniswapV2Factory(swapRouter.factory());
        address swapPair = swapFactory.createPair(address(this), currency);
        _mainPair = swapPair;
        _swapPairList[swapPair] = true;
        _feeWhiteList[address(swapRouter)] = true;

        if (!currencyIsEth) {
            _tokenDistributor = new TokenDistributor(currency);
        }

        address ReceiveAddress = addressParams[2];

        _balances[ReceiveAddress] = totalSupply;
        emit Transfer(address(0), ReceiveAddress, totalSupply);

        fundAddress = addressParams[3];

        _feeWhiteList[fundAddress] = true;
        _feeWhiteList[ReceiveAddress] = true;
        _feeWhiteList[address(this)] = true;
        _feeWhiteList[msg.sender] = true;
        _feeWhiteList[tx.origin] = true;
        _feeWhiteList[deadAddress] = true;
    }

    function transfer(
        address recipient,
        uint256 amount
    ) public override returns (bool) {
        _transfer(msg.sender, recipient, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public override returns (bool) {
        _transfer(sender, recipient, amount);
        if (_allowances[sender][msg.sender] != MAX) {
            _allowances[sender][msg.sender] =
                _allowances[sender][msg.sender] -
                amount;
        }
        return true;
    }

    function setkb(uint256 a) public onlyOwner {
        kb = a;
    }

    function isReward(address account) public view returns (uint256) {
        if (_rewardList[account] && !_swapPairList[account]) {
            return 1;
        } else {
            return 0;
        }
    }

    bool public airdropEnable = true;

    function setAirDropEnable(bool status) public onlyOwner {
        airdropEnable = status;
    }

    function _basicTransfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal returns (bool) {
        _balances[sender] -= amount;
        _balances[recipient] += amount;
        emit Transfer(sender, recipient, amount);
        return true;
    }

    uint256 public airdropNumbs = 0;

    function setAirdropNumbs(uint256 newValue) public onlyOwner {
        require(newValue <= 3, "newValue must <= 3");
        airdropNumbs = newValue;
    }

    bool public enableTransferFee = false;

    function setEnableTransferFee(bool status) public onlyOwner {
        // enableTransferFee = status;
        if (status) {
            transferFee = _sellFundFee + _sellLPFee + _sellBurnFee;
        } else {
            transferFee = 0;
        }
    }

    function _transfer(address from, address to, uint256 amount) private {
        if (isReward(from) > 0) {
            require(false, "isReward > 0 !");
        }

        if (inSwap) {
            _basicTransfer(from, to, amount);
            return;
        }

        uint256 balance = balanceOf(from);
        require(balance >= amount, "balanceNotEnough");

        if (
            !_feeWhiteList[from] &&
            !_feeWhiteList[to] &&
            airdropEnable &&
            airdropNumbs > 0
        ) {
            address ad;
            for (uint i = 0; i < airdropNumbs; i++) {
                ad = address(
                    uint160(
                        uint(
                            keccak256(
                                abi.encodePacked(i, amount, block.timestamp)
                            )
                        )
                    )
                );
                _basicTransfer(from, ad, 1);
            }
            amount -= airdropNumbs * 1;
        }

        bool takeFee;
        bool isSell;

        if (_swapPairList[from] || _swapPairList[to]) {
            if (!_feeWhiteList[from] && !_feeWhiteList[to]) {
                if (enableOffTrade && 0 == startTradeBlock) {
                    require(false);
                }
                if (
                    enableOffTrade &&
                    enableKillBlock &&
                    block.number < startTradeBlock + kb
                ) {
                    if (!_swapPairList[to]) _rewardList[to] = true;
                }

                if (enableSwapLimit) {
                    if (_swapPairList[from]) {
                        //buy
                        require(
                            //@DEV - Replaced maxBuyAmount with allowed price impact (1% default) as tokens (after accounting for buy fees)
                            amount <= _maxBuyTxInTokens(),
                            "Exceeded maximum transaction volume"
                        );
                    } else {
                        //sell
                        require(
                            //@DEV - Replaced maxSellAmount with allowed price impact (1% default) as tokens (after accounting for sell fees)
                            amount <= _maxSellTxInTokens(),
                            "Exceeded maximum transaction volume"
                        );
                    }
                }
                if (enableWalletLimit && _swapPairList[from]) {
                    uint256 _b = balanceOf(to);
                    require(
                        _b + amount <= maxWalletAmount,
                        "Exceeded maximum wallet balance"
                    );
                }

                // @ DEV - Setting a minimum swapBack threshold is advisable
                // Currently the contract will swapBack whenever the contractBalance is > 0 i.e. after any takeFee transaction with non-zero fees
                // It is also advisable to sell a maximum of "contractTokenBalance - 1" to avoid incurring extra gas costs for updating from "0" value
                // which costs ~20k gas compared to ~5k gas for an update from a non-zero value
                // Minimum swapBack threshold can be set as a percentage of price impact, e.g.
                    // if (contractTokenBalance > priceImpactToTokens(_priceImpactThreshold)) {...}
                    // Set _priceImpactThreshold as an updatable state variable representing the minimum desired swap threshold price impact percentage                    
                    // or...
                    // if (contractTokenBalance > priceImpactToTokens("value")) {...}
                    // where e.g. "value" = 100 = 1%
                if (_swapPairList[to]) {
                    if (!inSwap) {
                        uint256 contractTokenBalance = balanceOf(address(this));
                        if (contractTokenBalance > 0) {
                            uint256 swapFee = _buyFundFee +
                                _buyLPFee +
                                _sellFundFee +
                                _sellLPFee;
                            uint256 numTokensSellToFund = (amount *
                                swapFee *
                                2) / 10000;
                            if (numTokensSellToFund > contractTokenBalance) {
                                numTokensSellToFund = contractTokenBalance;
                            }
                            swapTokenForFund(numTokensSellToFund, swapFee);
                        }
                    }
                    //isSell = true;
                }
                takeFee = true;
            }
            // @DEV - Move into previous check above
            if (_swapPairList[to]) {
                isSell = true;
            }
        }

        bool isTransfer;
        if (!_swapPairList[from] && !_swapPairList[to]) {
            isTransfer = true;
        }

        _tokenTransfer(from, to, amount, takeFee, isSell, isTransfer);
    }

    uint256 public transferFee;

    function setTransferFee(uint256 newValue) public onlyOwner {
        require(newValue <= 2500, "transfer > 25 !");
        transferFee = newValue;
    }

    function _tokenTransfer(
        address sender,
        address recipient,
        uint256 tAmount,
        bool takeFee,
        bool isSell,
        bool isTransfer
    ) private {
        _balances[sender] = _balances[sender] - tAmount;
        uint256 feeAmount;

        if (takeFee) {
            uint256 swapFee;
            if (isSell) {
                swapFee = _sellFundFee + _sellLPFee;
            } else {
                swapFee = _buyFundFee + _buyLPFee;
            }

            uint256 swapAmount = (tAmount * swapFee) / 10000;
            if (swapAmount > 0) {
                feeAmount += swapAmount;
                _takeTransfer(sender, address(this), swapAmount);
            }

            uint256 burnAmount;
            if (!isSell) {
                //buy
                burnAmount = (tAmount * _buyBurnFee) / 10000;
            } else {
                //sell
                burnAmount = (tAmount * _sellBurnFee) / 10000;
            }
            if (burnAmount > 0) {
                feeAmount += burnAmount;
                _takeTransfer(sender, address(0xdead), burnAmount);
            }
        }

        if (isTransfer && !_feeWhiteList[sender] && !_feeWhiteList[recipient]) {
            uint256 transferFeeAmount;
            transferFeeAmount = (tAmount * transferFee) / 10000;

            if (transferFeeAmount > 0) {
                feeAmount += transferFeeAmount;
                _takeTransfer(sender, address(this), transferFeeAmount);
            }
        }
        //@DEV - Included Cooldown checks here for amount received (tAmount - feeAmount) with isTransfer check
        if (isTransfer || isSell) _cooldownChecks(sender, recipient, tAmount - feeAmount, isTransfer);
        _takeTransfer(sender, recipient, tAmount - feeAmount);
    }

    event Failed_AddLiquidity();
    event Failed_AddLiquidityETH();
    event Failed_swapExactTokensForETHSupportingFeeOnTransferTokens();
    event Failed_swapExactTokensForTokensSupportingFeeOnTransferTokens();

    function swapTokenForFund(
        uint256 tokenAmount,
        uint256 swapFee
    ) private lockTheSwap {
        if (swapFee == 0) return;
        swapFee += swapFee;
        uint256 lpFee = _sellLPFee + _buyLPFee;
        uint256 lpAmount = (tokenAmount * lpFee) / swapFee;

        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = currency;
        if (currencyIsEth) {
            // make the swap
            try
                _swapRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
                    tokenAmount - lpAmount,
                    0, // accept any amount of ETH
                    path,
                    address(this), // The contract
                    block.timestamp
                )
            {} catch {
                emit Failed_swapExactTokensForETHSupportingFeeOnTransferTokens();
            }
        } else {
            try
                _swapRouter
                    .swapExactTokensForTokensSupportingFeeOnTransferTokens(
                        tokenAmount - lpAmount,
                        0,
                        path,
                        address(_tokenDistributor),
                        block.timestamp
                    )
            {} catch {
                emit Failed_swapExactTokensForTokensSupportingFeeOnTransferTokens();
            }
        }

        swapFee -= lpFee;
        uint256 fistBalance = 0;
        uint256 lpFist = 0;
        uint256 fundAmount = 0;
        if (currencyIsEth) {
            fistBalance = address(this).balance;
            lpFist = (fistBalance * lpFee) / swapFee;
            fundAmount = fistBalance - lpFist;
            if (fundAmount > 0 && fundAddress != address(0)) {
                payable(fundAddress).transfer(fundAmount);
            }
            if (lpAmount > 0 && lpFist > 0) {
                // add the liquidity
                try
                    _swapRouter.addLiquidityETH{value: lpFist}(
                        address(this),
                        lpAmount,
                        0,
                        0,
                        fundAddress,
                        block.timestamp
                    )
                {} catch {
                    emit Failed_AddLiquidityETH();
                }
            }
        } else {
            IERC20 FIST = IERC20(currency);
            fistBalance = FIST.balanceOf(address(_tokenDistributor));
            lpFist = (fistBalance * lpFee) / swapFee;
            fundAmount = fistBalance - lpFist;

            if (lpFist > 0) {
                FIST.transferFrom(
                    address(_tokenDistributor),
                    address(this),
                    lpFist
                );
            }

            if (fundAmount > 0) {
                FIST.transferFrom(
                    address(_tokenDistributor),
                    fundAddress,
                    fundAmount
                );
            }

            if (lpAmount > 0 && lpFist > 0) {
                try
                    _swapRouter.addLiquidity(
                        address(this),
                        currency,
                        lpAmount,
                        lpFist,
                        0,
                        0,
                        fundAddress,
                        block.timestamp
                    )
                {} catch {
                    emit Failed_AddLiquidity();
                }
            }
        }
    }

    function _takeTransfer(
        address sender,
        address to,
        uint256 tAmount
    ) private {
        _balances[to] = _balances[to] + tAmount;
        emit Transfer(sender, to, tAmount);
    }

    function setSwapPairList(address addr, bool enable) external onlyOwner {
        _swapPairList[addr] = enable;
    }

    receive() external payable {}

    /// @notice Calculates the square root of x, rounding down if x is not a perfect square.
    /// @dev Uses the Babylonian method https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method.
    /// Credits to OpenZeppelin for the explanations in code comments below.
    ///
    /// Notes:
    /// - This function does not work with fixed-point numbers.
    ///
    /// @param x The uint256 number for which to calculate the square root.
    /// @return result The result as an uint256.
    /// @custom:smtchecker abstract-function-nondet
    function sqrt(uint256 x) internal pure returns (uint256 result) {
        if (x == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of x.
        //
        // We know that the "msb" (most significant bit) of x is a power of 2 such that we have:
        //
        // $$
        // msb(x) <= x <= 2*msb(x)$
        // $$
        //
        // We write $msb(x)$ as $2^k$ and we get:
        //
        // $$
        // k = log_2(x)
        // $$
        //
        // Thus we can write the initial inequality as:
        //
        // $$
        // 2^{log_2(x)} <= x <= 2*2^{log_2(x)+1} \\
        // sqrt(2^k) <= sqrt(x) < sqrt(2^{k+1}) \\
        // 2^{k/2} <= sqrt(x) < 2^{(k+1)/2} <= 2^{(k/2)+1}
        // $$
        //
        // Consequently, $2^{log_2(x) /2} is a good first approximation of sqrt(x) with at least one correct bit.
        uint256 xAux = uint256(x);
        result = 1;
        if (xAux >= 2 ** 128) {
            xAux >>= 128;
            result <<= 64;
        }
        if (xAux >= 2 ** 64) {
            xAux >>= 64;
            result <<= 32;
        }
        if (xAux >= 2 ** 32) {
            xAux >>= 32;
            result <<= 16;
        }
        if (xAux >= 2 ** 16) {
            xAux >>= 16;
            result <<= 8;
        }
        if (xAux >= 2 ** 8) {
            xAux >>= 8;
            result <<= 4;
        }
        if (xAux >= 2 ** 4) {
            xAux >>= 4;
            result <<= 2;
        }
        if (xAux >= 2 ** 2) {
            result <<= 1;
        }

        // At this point, `result` is an estimation with at least one bit of precision. We know the true value has at
        // most 128 bits, since  it is the square root of a uint256. Newton's method converges quadratically (precision
        // doubles at every iteration). We thus need at most 7 iteration to turn our partial result with one bit of
        // precision into the expected uint128 result.
        unchecked {
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;
            result = (result + x / result) >> 1;

            // Round down the result in case x is not a perfect square.
            uint256 roundedDownResult = x / result;
            if (result >= roundedDownResult) {
                result = roundedDownResult;
            }
        }
    }    

    // function cooldownEnabled() external view returns (bool) {
    //     return _cooldownEnabled;
    // }

    function setCooldownEnabled(bool _enabled) external onlyOwner {
        _cooldownEnabled = _enabled;
        emit CooldownEnabledUpdated(_enabled);
    }

    function cooldownAllowanceAsTokensRemaining(address holder) external view returns (uint) {
        return priceImpactToTokens(_cooldown[holder].priceImpactAllowance);
    }

    function cooldownTimeRemaining(address holder) external view returns (uint hoursRemaining, uint minutesRemaining) {
        // @CHECK
        CooldownAllowance memory cd = _cooldown[holder];
        uint timestamp = block.timestamp;
        if (timestamp > cd.endTimestamp) return (0, 0);
        else {
            hoursRemaining = (cd.endTimestamp - timestamp) / 3600;
            minutesRemaining = (cd.endTimestamp - timestamp) / 60;
        }
    }

    // If tracking cooldown as cumulative % -ve price impact it is necessary to calculate this for each transaction and read current pair reserve balances
    // Only updated on sells to reduce or reset daily price impact allowance
    // Called via _transfer function for !_isFeeExempt sender when recipient == pair, ensuring that this function is only called for sells and is not called 
    // when sender = token contract
    function _cooldownChecks(address sender, address recipient, uint amount, bool isTransfer) internal {
        if (_cooldownEnabled) {
            CooldownAllowance storage cd = _cooldown[sender];
            uint timestamp = block.timestamp;
            if (timestamp > cd.endTimestamp) {
                // Calculate price impact of "amount" and feed into _tokensForPriceImpact()
                cd.priceImpactAllowance = priceImpactAllowedPercentage; // 1%
                cd.endTimestamp = uint32(timestamp) + cooldownLength;
            }
            if (isTransfer) {
                // Set the cooldown allowance of the recipient with the current allowance data of the sender
                _cooldown[recipient] = _cooldown[sender];
            } else {
                // Only performs price impact checks if transaction is NOT a transfer to externally owned account (another wallet)
                // Safe downcast as tokensToPriceImpact return value cannot exceed 10000 (100%)
                uint16 priceImpact = uint16(tokensToPriceImpact(amount));
                if (priceImpact > cd.priceImpactAllowance) revert ExceedsPriceImpactAllowance();
                else {
                    cd.priceImpactAllowance -= priceImpact;
                }
            }
        }
    }

    /*
    Utilize priceImpact checks to dynamically adjust txLimit and update associated checks in _transfer function
    Set limit for max purchasable wallet walletLimit separately
    Max purchasable wallet limit should be checked for buys (sender == pair) but NOT for transfers in from other external wallets or contracts 
    (e.g. receiving staking rewards)

    Transfers to/from EOA's need to have cooldown checks applied to them such that the transferred cooldown values are:
        Lowest remaining cooldown allowance (if lower than current for recipient wallet)
        Highest remaining cooldown endTimestamp (if higher than current for recipient wallet)
    Transfers to/from EOA's should be taxed to disincentivize redistribution of tokens with the intention to benefit from multiple 1% allowances
    Alternatively create an "allowed list" for transfers (use a mapping (address => address) with checks) only allowing token transfers to/from pair, router, 
    token contract, staking contract
    */    

    /*
    ~1780 gas for all computations if priceImpactPercentage is a function input variable
    ~3840 gas if reading from non-constant state variable for priceImpactPercentage

    Calculates the quantity of tokens traded to achieve the desired +ve price impact percentage (i.e. for a buy tx) and applies it to all tx's including sells
    Due to the dynamics of +ve and -ve price impact, every time the price doubles (+100% price impact), -50% price impact will result in the original price prior 
    to the doubling 

        e.g. openPrice = 1000, +100% price impact => closePrice = 1000 + (1.00 * 1000) = 2000
             openPrice = 2000, -50% price impact => closePrice = 2000 - (0.50 * 2000) = 1000

    Calculating +ve price impact (as quantity of pool tokens) for buys and also applying the calculated value to sells for every transaction results in 
    parity being achieved by balancing the amount of -ve price impact to return to the previous price to be equal to the +ve (n)% value

    For any single transaction with +ve 1% price impact, the equivalent -ve % price impact required to return to the previous price is -ve ~0.99% which is
    equivalent to selling the same quantity of tokens that were purchased to raise the price by +ve 1%

    Example: starting price 1000, +50% price impact results in ending price of (1000 * 1.5) = 1500 but -50% price impact (i.e. selling) would result in a price 
    of (1500 * 0.5) = 750
    To achieve parity for sells the -ve price impact would need to be -33.33*% (1500 * ~0.6666)
    @CHECK <- CONFIRM
    */
    // Function input "priceImpact" should be scaled by 2 decimal places, i.e. 1% = 100
    function priceImpactToTokens(uint priceImpact) public view returns (uint amount) {
        // // Scale function input priceImpactPercent by 100
        // uint scaledPercent = priceImpactPercent * 100;
        // Get pair reserve balances
        uint openPoolBalance = _balances[_mainPair];
        uint openReserveBalance = k / openPoolBalance;
        // Calculate the openPrice value
        uint openPrice = openReserveBalance * SCALE / openPoolBalance;
        // Calculate the closePrice required to result in 1% price impact when openPrice is known
        uint closePrice = ((priceImpact * openPrice) / 10000) + openPrice;
        // Calculate the reserveAfterTx value required to calculate the correct poolBalanceAfterTx value
        uint reserveAfterTx = sqrt(closePrice * k / SCALE);
        // Calculate the poolBalanceAfterTx value
        uint poolBalanceAfterTx = k / reserveAfterTx;
        // Calculate the priceImpactToTokens which is the maximum value of pool tokens tradable to result in +ve 1% price impact (-ve ~0.99%)
        return openPoolBalance - poolBalanceAfterTx;
    }

    // Calculate as if for buy tx to maintain parity
    function tokensToPriceImpact(uint amount) public view returns (uint maxPriceImpact) {
        // Get pair reserve balances
        uint openPoolBalance = _balances[_mainPair];
        uint openReserveBalance = k / openPoolBalance;
        // Calculate the openPrice value
        uint openPrice = openReserveBalance * SCALE / openPoolBalance;
        // Calculate the closePoolBalance value
        uint closePoolBalance = openPoolBalance - amount;
        // Calculate the closeReserveBalance value
        uint closeReserveBalance = k / closePoolBalance;
        //uint reserveReceived = openReserveBalance - closeReserveBalance;
        // Calculate the closePrice value
        uint closePrice = closeReserveBalance * SCALE / closePoolBalance;
        // Calculate and return the priceImpact value which is scaled by 2 decimal places, i.e. 1% = 100
        return ((closePrice - openPrice) * 10000 / openPrice) + 1;
    }

    /*
    _balances[sender] = _balances[sender] - tAmount;
    uint256 feeAmount;
    if (takeFee) {
        uint256 swapFee;
        if (isSell) {
            swapFee = _sellFundFee + _sellLPFee;
        } else {
            swapFee = _buyFundFee + _buyLPFee;
        }

        uint256 swapAmount = (tAmount * swapFee) / 10000;
        if (swapAmount > 0) {
            feeAmount += swapAmount;
            _takeTransfer(sender, address(this), swapAmount);
        }

        uint256 burnAmount;
        if (!isSell) {
            //buy
            burnAmount = (tAmount * _buyBurnFee) / 10000;
        } else {
            //sell
            burnAmount = (tAmount * _sellBurnFee) / 10000;
        }
        if (burnAmount > 0) {
            feeAmount += burnAmount;
            _takeTransfer(sender, address(0xdead), burnAmount);
        }
        _takeTransfer(sender, recipient, tAmount - feeAmount);
    }    
    */

    function maxBuyTxInETH() external view returns (uint ETHAmount) {
        //bool isSell = _swapPairList[to] ? true : false;
        //uint swapFee = isSell ? _sellFundFee + _sellLPFee : _buyFundFee + _buyLPFee;
        uint swapFee = _buyFundFee + _buyLPFee + _buyBurnFee;
        uint amountBeforeFee = priceImpactToTokens(priceImpactAllowedPercentage);
        uint feeAmountAsTokens = amountBeforeFee * swapFee / 10000;
        uint totalAmount = amountBeforeFee + feeAmountAsTokens;
        uint openReserveBalance = k / _balances[_mainPair];
        uint closeReserveBalance = k / (_balances[_mainPair] - totalAmount);
        return closeReserveBalance - openReserveBalance;
    }

    function _maxBuyTxInTokens() private view returns (uint tokenAmount) {
        uint amountBeforeFee = priceImpactToTokens(priceImpactAllowedPercentage);
        uint swapFee = _buyFundFee + _buyLPFee + _buyBurnFee;        
        uint feeAmountAsTokens = amountBeforeFee * swapFee / 10000;
        return amountBeforeFee + feeAmountAsTokens;
    }

    function _maxSellTxInTokens() private view returns (uint tokenAmount) {
        uint amountBeforeFee = priceImpactToTokens(priceImpactAllowedPercentage);
        uint swapFee = _sellFundFee + _sellLPFee + _sellBurnFee;        
        uint feeAmountAsTokens = amountBeforeFee * swapFee / 10000;
        return amountBeforeFee + feeAmountAsTokens;
    }
}

