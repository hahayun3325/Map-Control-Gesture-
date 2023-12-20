package com.example.finalhand1;

import android.util.Log;

import com.google.mediapipe.formats.proto.LandmarkProto;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class RecHands {
    private  static int testn=0,sumn=0;

    public static String handGestureDiscriminator(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        if (multiHandLandmarks.isEmpty()) {
            return "NO HAND";
        }

        // 为每个手指设置一个flag来表示当前手指的开闭状态
        boolean thumbIsOpen = false;
        boolean firstFingerIsOpen = false;
        boolean secondFingerIsOpen = false;
        boolean thirdFingerIsOpen = false;
        boolean fourthFingerIsOpen = false;

        // 遍历所有的手
        for (LandmarkProto.NormalizedLandmarkList landmarks : multiHandLandmarks) {

            // 获取当前手的21个关键点
            List<LandmarkProto.NormalizedLandmark> landmarkList = landmarks.getLandmarkList();

            // 大拇指与其他四根手指的张开状态不一样，大拇指横向张开，其他手指向上张开
            // 对大拇指是否闭合的判断是要在 X 轴上，而其他的是在 Y 轴上判断
            // 而且可能还需要考虑到左右手，因此大拇指要另外拎出来判断，其他的则可以用循环解决

            // 设置一个相对固定点，这里是大拇指第二关节
            float FixKeyPoint = landmarkList.get(2).getX();

            // 右手大拇指判断是否闭合
            if (FixKeyPoint < landmarkList.get(9).getX()) {      //当固定点x坐标小于中指根部时，则为右手
                // 当第二关节和指尖都小于固定点时，大拇指为张开状态
                if (landmarkList.get(3).getX() < FixKeyPoint && landmarkList.get(4).getX() < FixKeyPoint) {
                    thumbIsOpen = true;
                }
            }
            // 左手大拇指判断是否闭合， 只是 x 轴镜像，原理与右手相同
            if (FixKeyPoint > landmarkList.get(9).getX()) {
                if (landmarkList.get(3).getX() > FixKeyPoint && landmarkList.get(4).getX() > FixKeyPoint) {
                    thumbIsOpen = true;
                }
            }

            // 其他四根手指可直接用循环
            for (int i = 6; i < 21; i = i + 4) {

                // 将第一关节设为相对固定点
                FixKeyPoint = landmarkList.get(i).getY();

                // 当第二关节低于第一关节且指尖低于第一关节时，则该手指为张开状态
                if (landmarkList.get(i + 1).getY() < FixKeyPoint && landmarkList.get(i + 2).getY() < landmarkList.get(i + 1).getY()) {
                    switch (i) {
                        case 6:
                            firstFingerIsOpen = true;
                            break;
                        case 10:
                            secondFingerIsOpen = true;
                            break;
                        case 14:
                            thirdFingerIsOpen = true;
                            break;
                        case 18:
                            fourthFingerIsOpen = true;
                            break;
                    }
                }
            }

            // 手势识别
            if (thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                return "FIVE";
            } else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                return "FOUR";
            } else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && !fourthFingerIsOpen) {
                return "THREE";
            } else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                return "TWO";
                // return "Yeah";
            } else if (!thumbIsOpen && firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                return "one";
            } else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && fourthFingerIsOpen) {
                return "SIX";
            } else if (!thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                return "fist";
            } else if (!firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen && isThumbNearFirstFinger(landmarkList.get(4), landmarkList.get(8))) {
                return "OK";
            } else {
                String info = " thumbIsOpen：" + thumbIsOpen + " firstFingerIsOpen：" + firstFingerIsOpen
                        + " secondFingerIsOpen：" + secondFingerIsOpen +
                        " thirdFingerIsOpen：" + thirdFingerIsOpen + " fourthFingerIsOpen：" + fourthFingerIsOpen;
                return "___";
            }
        }
        return "___";
    }

    public static final String myTAG="730music";
    // 改进的静态手势识别方法
    public static String handGestureDiscriminator_Pro(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        if (multiHandLandmarks.isEmpty()) {
            return "NO HAND";
        }

        // 为每个手指设置一个flag来表示当前手指的开闭状态
        boolean thumbIsOpen = false;
        boolean thumbIsOpenDown = false;
        boolean firstFingerIsOpen = false;
        boolean secondFingerIsOpen = false;
        boolean thirdFingerIsOpen = false;
        boolean fourthFingerIsOpen = false;


        for (LandmarkProto.NormalizedLandmarkList landmarks : multiHandLandmarks) {

            List<LandmarkProto.NormalizedLandmark> landmarkList = landmarks.getLandmarkList();

            LandmarkProto.NormalizedLandmark wrist = landmarkList.get(0);                         // 获取手腕的坐标
            LandmarkProto.NormalizedLandmark middleFinger_MCP = landmarkList.get(9);              // 获取中指根部坐标

            // 中指根部与手腕关键点连线相对于x轴的角度
            double ang_Radian = getAngleAB_AC(wrist.getX(), wrist.getY(), middleFinger_MCP.getX(), middleFinger_MCP.getY(),
                    wrist.getX() + 0.1, wrist.getY());
            int ang_Degree = radian2Degree(ang_Radian);     //弧度转角度


            if (ang_Degree >= 45 && ang_Degree <= 135) { // 当手掌处于相对竖直状态的时候

                // 设置一个相对固定点，这里是大拇指第二关节
                float FixKeyPoint = landmarkList.get(2).getX();

                // 当第二关节和指尖都小于固定点时，大拇指为张开状态
//                if (landmarkList.get(3).getX() < FixKeyPoint && landmarkList.get(4).getX() < FixKeyPoint) {
//                    thumbIsOpen = true;
//                }
                if (landmarkList.get(3).getX() < FixKeyPoint && landmarkList.get(4).getX() < landmarkList.get(3).getX()) {
                    // 拇指伸展：从根部到指尖，关节对应的横坐标依次减小
                    thumbIsOpen = true;
                    // : 9/23/2022  区分finishsign和changevol以及fist
                    if(isThumbNearFirstFinger(landmarkList.get(4), landmarkList.get(6))){
                        // 当拇指和食指关节6距离较近，认为处于fist握拳手势，判定拇指未伸展
                        thumbIsOpen=false;
                    }
                }
                if (wrist.getY() > middleFinger_MCP.getY()) {
                    // 竖直上状态
                    // 其他四根手指可直接用循环
                    for (int i = 6; i < 21; i = i + 4) {

                        // 将第一关节设为相对固定点
                        FixKeyPoint = landmarkList.get(i).getY();

                        // 当第二关节小于第一关节且指尖小于第一关节时，则该手指为张开状态
                        if (landmarkList.get(i + 1).getY() < FixKeyPoint && landmarkList.get(i + 2).getY() < landmarkList.get(i + 1).getY()) {
                            // 手指展开：关节自上到下纵坐标依次增大
                            switch (i) {
                                case 6:
                                    firstFingerIsOpen = true;
                                    break;
                                case 10:
                                    secondFingerIsOpen = true;
                                    break;
                                case 14:
                                    thirdFingerIsOpen = true;
                                    break;
                                case 18:
                                    fourthFingerIsOpen = true;
                                    break;
                            }
                        }
                    }
                    // TODO: 8/20/2022 将判断条件更为严格——应为修改后的地图缩放更为灵敏 
//                    if(landmarkList.get(8).getX() < landmarkList.get(7).getX()&&landmarkList.get(7).getX() < landmarkList.get(6).getX()&&landmarkList.get(6).getX() < landmarkList.get(5).getX())
//                    {
//                        firstFingerIsOpen=true;
//                    }
                    /*
                    对于第一手指伸展的判断
                        针对手势changeVOl，添加的通过关键关节的横坐标的判断，在第一手指蜷缩状态下(握拳状态)会出现横坐标判断不准确的情况，从而误判为第一手指处于伸展状态,进而将返回手势finish sign判断为changevol
                     */
//                    Log.d(mytag, "当前拇指情况thumb:"+thumbIsOpen+"\n横坐标:4号点"+landmarkList.get(4).getX()+"\n3号点:"+landmarkList.get(3).getX()+"\n2号点："+FixKeyPoint+"\n"+"旋转角度:"+ang_Degree);
//                    Log.d(myTAG, "\n拇指:"+thumbIsOpen+"\nfirstFingerIsOpen:"+firstFingerIsOpen+"\n secondFingerIsOpen："+secondFingerIsOpen+"\n thirdFingerIsOpen："+thirdFingerIsOpen+"\n fourthFingerIsOpen："+fourthFingerIsOpen+"\n");
//                    Log.d(myTAG, "\n当前拇指和食指间距"+Double.toString(getEuclideanDistanceAB(landmarkList.get(4).getX(),landmarkList.get(4).getY(), landmarkList.get(8).getX(),landmarkList.get(8).getY())));
                    // 手势识别
                    if ( secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen && isThumbNearFirstFinger(landmarkList.get(4), landmarkList.get(8))) {
                        return "OK";
                    }else if (thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                        return "handStopMusic";
                    }  else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                        return "四";
                    } else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "THREE";
                    }
                    else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen&&isThumbNearFirstFinger(landmarkList.get(8),landmarkList.get(12))) {
                        return "Close2";//当食指和中指之间靠近的时候，才认为是对应的手势
                    }else if (!thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "TWO";
                    } else if (!thumbIsOpen && firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "one";
                    }else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && fourthFingerIsOpen) {
                        return "SIX";
                    }
                    // : 7/29/2022
                    else if (!secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        /*
                        当1手指接近于水平状态时，根据实验测试，（由于1手指伸展判断通过关键点的纵坐标）会被认为只有拇指伸展，导致判断结果是finishsign
                            在2 3 4手指处于闭合状态下，判断changevol手势 有两种情况
                                1手指处于水平状态
                                不成功，因为使用拇指和1手指指尖之间的间距作为判断依据时，当1手指被遮挡的情况下，mediapipe对于手指关键点的计算出现较大误差，会在握拳情况下判断手指间距为0.09左右范围内
                                1手指不处于水平状态
                            最终解决方案，1手指伸缩状态的判断在按照y坐标判断的基础上继续使用x坐标作为判断依据

                         */
//                        if (changevol_begin<getEuclideanDistanceAB(landmarkList.get(4).getX(), landmarkList.get(4).getY(), landmarkList.get(8).getX(), landmarkList.get(8).getY()) && getEuclideanDistanceAB(landmarkList.get(4).getX(), landmarkList.get(4).getY(), landmarkList.get(8).getX(), landmarkList.get(8).getY()) < changevol_index) {
//                            return "ChangeVol";//1手指处于水平状态
//                        }
//                        else
                        double changevol_index=100;// 通过手指间距离对于changvol手势判断
                        // 计算changevol手势关键手指的间距
                        double changevol_dist=getEuclideanDistanceAB(landmarkList.get(4).getX()*image_width, landmarkList.get(4).getY()*image_height, landmarkList.get(8).getX()*image_width, landmarkList.get(8).getY()*image_height);
//                        Log.d("changvol", "当前手指间距"+changevol_dist);
                        if ((firstFingerIsOpen&&thumbIsOpen)||(thumbIsOpen&&changevol_dist< changevol_index)){
//                            Log.d(myTAG, "changeVOl相关关键点的位置:\n5点:("+landmarkList.get(5).getX()+","+landmarkList.get(5).getY()+")\n6点:("+landmarkList.get(6).getX()+","+landmarkList.get(6).getY()+")\n7点:("+landmarkList.get(7).getX()+","+landmarkList.get(7).getY()+")"+")\n8点:("+landmarkList.get(8).getX()+","+landmarkList.get(8).getY()+")"//
//                            +"\n4点:("+landmarkList.get(4).getX()+","+landmarkList.get(4).getY()+")");
                            Log.d("changvol", "changevol手势判断成功");
                            return "ChangeVol";//1手指不处于水平状态
                        }
                        else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                            return "FINISHSIGN";
                        }
                        else if (!thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                            return "fist";//拳头
                        }
                        // : 7/29/2022 修改后的手势判别 导致比心手势的判别同样被覆盖掉了
                        else if (firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen && isThumbNearFirstFinger(landmarkList.get(4), landmarkList.get(8))) {
                            return "比心";
                        } else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                            return "FINISHSIGN";
                        } else {
                            String info = " thumbIsOpen：" + thumbIsOpen + " firstFingerIsOpen：" + firstFingerIsOpen
                                    + " secondFingerIsOpen：" + secondFingerIsOpen +
                                    " thirdFingerIsOpen：" + thirdFingerIsOpen + " fourthFingerIsOpen：" + fourthFingerIsOpen;
                            return "___";
                        }
                    }

                } else {   // 竖直下状态

                    // 其他四根手指可直接用循环
                    for (int i = 6; i < 21; i = i + 4) {

                        // 将第一关节纵坐标设为相对固定点
                        FixKeyPoint = landmarkList.get(i).getY();

                        // 当第二关节大于第一关节且指尖大于第一关节时，则该手指为张开状态
                        if (landmarkList.get(i + 1).getY() > FixKeyPoint && landmarkList.get(i + 2).getY() > landmarkList.get(i + 1).getY()) {
                            switch (i) {
                                case 6:
                                    firstFingerIsOpen = true;
                                    break;
                                case 10:
                                    secondFingerIsOpen = true;
                                    break;
                                case 14:
                                    thirdFingerIsOpen = true;
                                    break;
                                case 18:
                                    fourthFingerIsOpen = true;
                                    break;
                            }
                        }
                    }

                    // 手势识别
                    if (!thumbIsOpen && firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "一下";
                    } else {
                        String info = " thumbIsOpen：" + thumbIsOpen + " firstFingerIsOpen：" + firstFingerIsOpen
                                + " secondFingerIsOpen：" + secondFingerIsOpen +
                                " thirdFingerIsOpen：" + thirdFingerIsOpen + " fourthFingerIsOpen：" + fourthFingerIsOpen;
                        return "___";
                    }

                }
            } else {    // 当手掌处于相对水平状态的时候

                // 设置一个相对固定点，这里是大拇指第二关节
                float FixKeyPoint = landmarkList.get(2).getY();

                // 当第二关节和指尖都小于固定点时，大拇指为张开状态（大拇指向上张开）
                if (landmarkList.get(3).getY() < FixKeyPoint && landmarkList.get(4).getY() < FixKeyPoint) {
                    thumbIsOpen = true;
                }

                // （大拇指向下张开）
                if (landmarkList.get(3).getY() > FixKeyPoint && landmarkList.get(4).getY() > FixKeyPoint) {
                    thumbIsOpenDown = true;
                }

                if (wrist.getX() > middleFinger_MCP.getX()) {    // 水平左状态
                    // 其他四根手指可直接用循环
                    for (int i = 6; i < 21; i = i + 4) {

                        // 将第一关节横坐标设为相对固定点
                        FixKeyPoint = landmarkList.get(i).getX();

                        // 当第二关节横坐标小于第一关节且指尖横坐标小于第一关节时，则该手指为张开状态
                        if (landmarkList.get(i + 1).getX() < FixKeyPoint && landmarkList.get(i + 2).getX() < landmarkList.get(i + 1).getX()) {
                            switch (i) {
                                case 6:
                                    firstFingerIsOpen = true;
                                    break;
                                case 10:
                                    secondFingerIsOpen = true;
                                    break;
                                case 14:
                                    thirdFingerIsOpen = true;
                                    break;
                                case 18:
                                    fourthFingerIsOpen = true;
                                    break;
                            }
                        }
                    }

                    // 手势识别
                    if (!thumbIsOpen && firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "一左";
                    } else if (thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                        return "handToLeft";

                    } else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "FINISHSIGN";
                    }else {
                        String info = " thumbIsOpen：" + thumbIsOpen + " firstFingerIsOpen：" + firstFingerIsOpen
                                + " secondFingerIsOpen：" + secondFingerIsOpen +
                                " thirdFingerIsOpen：" + thirdFingerIsOpen + " fourthFingerIsOpen：" + fourthFingerIsOpen;
                        return "___";
                    }

                } else {   // 水平右的状态时

                    // 其他四根手指可直接用循环
                    for (int i = 6; i < 21; i = i + 4) {

                        // 将第一关节横坐标设为相对固定点
                        FixKeyPoint = landmarkList.get(i).getX();

                        // 当第二关节横坐标大于第一关节且指尖横坐标大于第一关节时，则该手指为张开状态
                        if (landmarkList.get(i + 1).getX() > FixKeyPoint && landmarkList.get(i + 2).getX() > landmarkList.get(i + 1).getX()) {
                            switch (i) {
                                case 6:
                                    firstFingerIsOpen = true;
                                    break;
                                case 10:
                                    secondFingerIsOpen = true;
                                    break;
                                case 14:
                                    thirdFingerIsOpen = true;
                                    break;
                                case 18:
                                    fourthFingerIsOpen = true;
                                    break;
                            }
                        }
                    }

                    // 手势识别
                    if (!thumbIsOpen && firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "一右";
                    } else if (thumbIsOpen && firstFingerIsOpen && secondFingerIsOpen && thirdFingerIsOpen && fourthFingerIsOpen) {
                        return "handToRight";
                    } else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "强";
                    } else if (thumbIsOpenDown && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "弱";
                    } else if (thumbIsOpen && !firstFingerIsOpen && !secondFingerIsOpen && !thirdFingerIsOpen && !fourthFingerIsOpen) {
                        return "FINISHSIGN";
                    }else {
                        String info = " thumbIsOpen：" + thumbIsOpen + " firstFingerIsOpen：" + firstFingerIsOpen
                                + " secondFingerIsOpen：" + secondFingerIsOpen +
                                " thirdFingerIsOpen：" + thirdFingerIsOpen + " fourthFingerIsOpen：" + fourthFingerIsOpen;
                        return "___";
                    }
                }

            }
        }
        return "___";
    }

    // 判断是否大拇指尖和食指指尖足够接近
    public static boolean isThumbNearFirstFinger(LandmarkProto.NormalizedLandmark point1, LandmarkProto.NormalizedLandmark point2) {
        double distance = getEuclideanDistanceAB(point1.getX(), point1.getY(), point2.getX(), point2.getY());
        return distance < 0.1;
    }

    // 计算两点之间的欧拉距离
    public static double getEuclideanDistanceAB(double a_x, double a_y, double b_x, double b_y) {
        double distance = Math.pow(a_x - b_x, 2) + Math.pow(a_y - b_y, 2);
        return Math.sqrt(distance);
    }


    public static Float CalculDis(float[] landmark_list_temp, int num1, int num2) {

        float node5_x = landmark_list_temp[5 * 2], node5_y = landmark_list_temp[5 * 2 + 1];//中指
        float node6_x = landmark_list_temp[6 * 2], node6_y = landmark_list_temp[6 * 2 + 1];//无名指
        Float Dis5_6 = (node5_x - node6_x) * (node5_x - node6_x) + (node5_y - node6_y) * (node5_y - node6_y);


        float x1 = landmark_list_temp[num1 * 2], y1 = landmark_list_temp[num1 * 2 + 1];
        float x2 = landmark_list_temp[num2 * 2], y2 = landmark_list_temp[num2 * 2 + 1];

        Float res = (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2);
        return res / Dis5_6;
    }

    //todo 按照不同手机 获得前置摄像头的分辨率宽和高
    final public static int image_width = 720;
    final public static int image_height = 1280;

    //获取手关节x，y位置坐标
    public static float[] getMultiHandLandmarksDebugXY(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        if (multiHandLandmarks.isEmpty()) {
            return null;
        }
        return calcLandmarkList(image_width, image_height, multiHandLandmarks);
    }

    //获取每个关节x，y坐标，并将NormalizedLandmark恢复为真实像素坐标
    public static float[] calcLandmarkList(int image_width, int image_height, List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        List<int[]> landmark_points = new ArrayList<>();
        //获取所有手的关节点列表，目前只有一只手
        for (LandmarkProto.NormalizedLandmarkList landmarks : multiHandLandmarks) {
            //获取获取每个关节x，y坐标
            for (LandmarkProto.NormalizedLandmark landmark : landmarks.getLandmarkList()) {
                int[] landmark_point_xy = new int[2];
                //将NormalizedLandmark恢复为真实像素坐标，判断真实像素坐标是否超出边界，选取合适值
                //X
                landmark_point_xy[0] = (int) (landmark.getX() * image_width) < image_width - 1 ? (int) (landmark.getX() * image_width) : image_width - 1;
                //Y
                landmark_point_xy[1] = (int) (landmark.getY() * image_height) < image_height - 1 ? (int) (landmark.getY() * image_height) : image_height - 1;
                //按手指21关节按顺序存入列表中，为下一步处理准备
                landmark_points.add(landmark_point_xy);
            }
        }
        return pre_process_landmark(landmark_points);
    }

    //将手指关节真实位置坐标进行预处理，将第一个关节设为【0,0】，其与关节为距离第一关节的相对位置（也就是用户）
    public static float[] pre_process_landmark(List<int[]> landmark_points) {
        int base_x = 0;
        int base_y = 0;
        List<Integer> listInt_abs = new ArrayList<>();      //存储关节相对位置绝对值
        List<Integer> listInt = new ArrayList<>();      //存储关节相对位置
        for (int i = 0; i < landmark_points.size(); i++) {
            //获取关节点x，y坐标
            int[] landmark_point_xy = landmark_points.get(i);
            if (i == 0) {
                //获取第一个关节位置坐标
                base_x = landmark_point_xy[0];
                base_y = landmark_point_xy[1];
            }
            //计算关节相对位置
            landmark_point_xy[0] = landmark_point_xy[0] - base_x;
            landmark_point_xy[1] = landmark_point_xy[1] - base_y;
            //存储关节相对位置
            listInt.add(landmark_point_xy[0]);
            listInt.add(landmark_point_xy[1]);
            //存储关节相对位置绝对值
            listInt_abs.add(Math.abs(landmark_point_xy[0]));
            listInt_abs.add(Math.abs(landmark_point_xy[1]));
        }
        //获取最大值
        int max_value = Collections.max(listInt_abs);
        float[] normalized_landmark = new float[42];
        for (int i = 0; i < listInt.size(); i++) {
            //归一化
            normalized_landmark[i] = listInt.get(i) / (float) max_value;
        }
        return normalized_landmark;
    }

    public static boolean fingerup(float[] landmark_list_temp, int fg1) {
        int num1 = fg1 * 4;
        int num2 = num1 - 1;
        float y1 = landmark_list_temp[num1 * 2 + 1];
        float y2 = landmark_list_temp[num2 * 2 + 1];
        return y1 < y2;

    }

    // A点为初始点，B为变化点，C是在X轴上的略微平移，即AC为水平向量
    // 计算两个向量之间的夹角（返回的为弧度）
    public static double getAngleAB_AC(double a_x, double a_y, double b_x, double b_y, double c_x, double c_y) {
        double ab_x = b_x - a_x;
        double ab_y = b_y - a_y;
        double ac_x = c_x - a_x;
        double ac_y = c_y - a_y;

        double abDotAc = ab_x * ac_x + ab_y * ac_y;
        double abValue = Math.sqrt(ab_x * ab_x + ab_y * ab_y);
        double acValue = Math.sqrt(ac_x * ac_x + ac_y * ac_y);

        double cos_ab_ac = abDotAc / (abValue * acValue);

        return Math.acos(cos_ab_ac);
    }

    // 将弧度转为度数
    public static int radian2Degree(double radian) {
        return (int) Math.floor(radian * 180. / Math.PI + 0.5);
    }


}
