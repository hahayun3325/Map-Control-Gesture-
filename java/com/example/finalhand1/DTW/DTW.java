package com.example.finalhand1.DTW;

/**
 *  A class that implements the awesome Dynamic Time Warping algorithm.
 *  Absolutely all credit for this implementation goes to the developers of the Gesture and Activity Recognition Toolkit, (GART).
 *  @http://trac.research.cc.gatech.edu/GART/browser/GART/weka/edu/gatech/gart/ml/weka/DTW.java?rev=9
 **/
public final class DTW {

    /** Defines the result for a Dynamic Time Warping operation. 定义一个DTW运行的结果*/
    public static class Result {
        /* Member Variables. */
        private final int[][] mWarpingPath;// 二维数组记录warping操作过程中动态规划的记录 并且注意二维数组传参过程中是如何使用的
        private final double  mDistance;
        /** Constructor. */
        public Result(final int[][] pWarpingPath, final double pDistance) {
            // Initialize Member Variables. 构造函数 对变量进行传参
            this.mWarpingPath = pWarpingPath;
            this.mDistance    = pDistance;
        }
        /* Getters. */
        public final int[][] getWarpingPath() { return this.mWarpingPath; }
        public final double getDistance() { return this.mDistance;    }
    }

    /** Default constructor for a class which implements dynamic time warping. 对于DTW一个对象的默认构造函数*/
    public DTW() { }

    /**
     * 用于使用DTW算法计算两个序列的相似度的情况
     * @param pSample 收集的样本序列长度
     * @param pTemplate 收集的模板序列的长度
     * @return
     */
    public Result compute(final float[] pSample, final float[] pTemplate) {
        // Declare Iteration Constants. 声明遍历使用到的常量
        final int lN = pSample.length;// 数组可以直接获得长度哟
        final int lM = pTemplate.length;
        // Ensure the samples are valid. 首先判断两个序列是否有效
        if(lN == 0 || lM == 0) {
            // Assert a bad result.
            return new Result(new int[][]{ /* No path data. */ }, Double.NaN);// 注意 距离为空，使用NaN
        }
        // Define the Scalar Qualifier. 定义标量限定符的情况
        int lK = 1;
        // Allocate the Warping Path. (Math.max(N, M) <= K < (N + M). 分配warping情况下路径
        // 要求限定符的移动范围在一个长度范围内：大于最长的序列长度并且要小于两个序列长度的和
        final int[][]    lWarpingPath  = new int[lN + lM][2];
        // Declare the Local Distances. 声明局部的距离 横纵坐标分别是两个序列点的编号，表示记录的是两个序列上点之间的距离
        final double[][] lL= new double[lN][lM];
        // Declare the Global Distances. 声明全局的距离
        final double[][] lG= new double[lN][lM];
        // Declare the MinimaBuffer. 定义最小的（缓冲）只存放3个数据
        final double[]   lMinimaBuffer = new double[3];
        // Declare iteration variables. 遍历时候的标识符 遍历循环使用的变量
        int i, j;
        // 首先获得对应序号点的距离情况——距离使用误差平方衡量，并且记录在局部数组中
        // Iterate the Sample. 外层遍历的是样本序列
        for(i = 0; i < lN; i++) {
            // Fetch the Sample.
            final float lSample = pSample[i];
            // Iterate the Template.
            for(j = 0; j < lM; j++) {// 模板序列的遍历
                // Calculate the Distance between the Sample and the Template for this Index.
                lL[i][j] = this.getDistanceBetween(lSample, pTemplate[j]);// 距离使用误差平方衡量
            }
        }

        // Initialize the Global. 对全局变量的初始化，将局部获得的距离情况赋值给全局
        lG[0][0] = lL[0][0];
        /**
         * 动态规划算法进行warping
         */
        // 动态规划前对网格空间的初始化——首先对边界两侧的距离进行更新，使用累加表示从模板或是样本序列开始到另一个序列相应序号的位置上需要的代价情况
        for(i = 1; i < lN; i++) {
            lG[i][0] = lL[i][0] + lG[i - 1][0];
        }

        for(j = 1; j < lM; j++) {
            lG[0][j] = lL[0][j] + lG[0][j - 1];
        }
        /*
        对于网格上除去边界上的所有点，动态规划得到的最短距离表示的是：从上左左上角得到的所有可能路径中选择一条最短的路径，并累加对应的代价(在局部矩阵中记录的 相邻位置达到当前序号位置需要的代价)
         */
        for (i = 1; i < lN; i++) {
            for (j = 1; j < lM; j++) {
                // Accumulate the path.
                lG[i][j] = (Math.min(Math.min(lG[i-1][j], lG[i-1][j-1]), lG[i][j-1])) + lL[i][j];
            }
        }

        // Update iteration varaibles. 更新遍历的变量 存疑
        i = lWarpingPath[lK - 1][0] = (lN - 1);// 代表样本序列
        j = lWarpingPath[lK - 1][1] = (lM - 1);// 代表模板序列

        // Whilst there are samples to process 存在需要加工的样本序列
        while ((i + j) != 0) {
            // Handle the offset. 处理解决抵消
            if(i == 0) {
                // Decrement the iteration variable. 每次遍历到头的时候， 循环变量需要-1
                j -= 1;
            }
            else if(j == 0) {
                // Decrement the iteration variable. 同样当模板序列遍历到头的时候，样本序列的符号同样-1
                i -= 1;
            }
            else {
                // Update the contents of the MinimaBuffer. 更新存在于缓冲区的内容
                lMinimaBuffer[0] = lG[i - 1][j];
                lMinimaBuffer[1] = lG[i][j - 1];
                lMinimaBuffer[2] = lG[i - 1][j - 1];
                // Calculate the Index of the Minimum. 计算最小的序号、索引
                final int lMinimumIndex = this.getMinimumIndex(lMinimaBuffer);
                // Declare booleans.
                final boolean lMinIs0 = (lMinimumIndex == 0);
                final boolean lMinIs1 = (lMinimumIndex == 1);
                final boolean lMinIs2 = (lMinimumIndex == 2);
                // Update the iteration components. 按照缓冲中数据的情况对循环变量进行更新
                i -= (lMinIs0 || lMinIs2) ? 1 : 0;
                j -= (lMinIs1 || lMinIs2) ? 1 : 0;
            }
            // Increment the qualifier. 限定符增加
            lK++;
            // Update the Warping Path.对于warping路径的更新 记录每个点对应位置选择的匹配点的情况 整个解空间当前在一个二维的网格上
            lWarpingPath[lK - 1][0] = i;
            lWarpingPath[lK - 1][1] = j;
        }

        // Return the Result. (Calculate the Warping Path and the Distance.)
        return new Result(this.reverse(lWarpingPath, lK), ((lG[lN - 1][lM - 1]) / lK));
    }

    /** Changes the order of the warping path, in increasing order. 将warping得到的路径修改成升序的顺序*/
    private int[][] reverse(final int[][] pPath, final int pK) {
        // Allocate the Path.对于路径的分配
        final int[][] lPath = new int[pK][2];
        // Iterate.
        for(int i = 0; i < pK; i++) {
            // Iterate.
            for (int j = 0; j < 2; j++) {
                // Update the Path.
                lPath[i][j] = pPath[pK - i - 1][j];
            }
        }
        // Return the Allocated Path.
        return lPath;
    }

    /** Computes a distance between two points. */
    protected double getDistanceBetween(double p1, double p2) {
        // Calculate the square error.
        return (p1 - p2) * (p1 - p2);
    }

    /** Finds the index of the minimum element from the given array. 获得数组中最小元素的序号*/
    protected final int getMinimumIndex(final double[] pArray) {
        // Declare iteration variables.
        int    lIndex = 0;
        double lValue = pArray[0];
        // Iterate the Array.
        for(int i = 1; i < pArray.length; i++) {
            // .Is the current value smaller?
            final boolean lIsSmaller = pArray[i] < lValue;
            // Update the search metrics.
            lValue = lIsSmaller ? pArray[i] : lValue;
            lIndex = lIsSmaller ?         i : lIndex;
        }
        // Return the Index.
        return lIndex;
    }

}