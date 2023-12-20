package com.example.finalhand1.MapControl;
import static com.example.finalhand1.MainActivity.num3;
import static com.example.finalhand1.MainActivity.num30;
import static com.example.finalhand1.MainActivity.num4;
import static com.example.finalhand1.MainActivity.num40;
import static com.example.finalhand1.MainActivity.num6;
import static com.example.finalhand1.MainActivity.num60;
import static com.example.finalhand1.MainActivity.num7;
import static com.example.finalhand1.MainActivity.num70;
import static com.example.finalhand1.MainActivity.num8;
import static com.example.finalhand1.MainActivity.num80;
import static com.example.finalhand1.RecHands.image_height;
import static com.example.finalhand1.RecHands.image_width;
import static com.example.finalhand1.RecHands.myTAG;
import static java.lang.Math.max;
import static java.lang.Math.min;

import android.Manifest;
import android.annotation.SuppressLint;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.graphics.SurfaceTexture;
import android.media.MediaPlayer;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.telecom.TelecomManager;
import android.telephony.PhoneStateListener;
import android.telephony.TelephonyManager;
import android.util.Log;
import android.util.Size;
import android.view.Gravity;
import android.view.LayoutInflater;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.view.ViewGroup;
import android.widget.AdapterView;
import android.widget.CompoundButton;
import android.widget.ImageView;
import android.widget.ListView;
import android.widget.ProgressBar;
import android.widget.Switch;
import android.widget.TextView;
import android.widget.Toast;

import androidx.annotation.NonNull;
import androidx.annotation.RequiresApi;
import androidx.appcompat.app.AppCompatActivity;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.preference.PreferenceManager;

import com.amap.api.location.AMapLocation;
import com.amap.api.location.AMapLocationClient;
import com.amap.api.location.AMapLocationClientOption;
import com.amap.api.location.AMapLocationListener;
import com.amap.api.maps.AMap;
import com.amap.api.maps.CameraUpdate;
import com.amap.api.maps.CameraUpdateFactory;
import com.amap.api.maps.MapView;
import com.amap.api.maps.MapsInitializer;
import com.amap.api.maps.model.CameraPosition;
import com.amap.api.maps.model.LatLng;
import com.amap.api.maps.model.MyLocationStyle;
import com.example.finalhand1.BrightnessAdapter;
import com.example.finalhand1.DTW.DTW;
import com.example.finalhand1.R;
import com.example.finalhand1.RecHands;
import com.example.finalhand1.mainmenuUI.MainMenu;
import com.example.finalhand1.mainmenuUI.MenuAdapter;
import com.google.mediapipe.components.CameraHelper;
import com.google.mediapipe.components.CameraXPreviewHelper;
import com.google.mediapipe.components.ExternalTextureConverter;
import com.google.mediapipe.components.FrameProcessor;
import com.google.mediapipe.components.PermissionHelper;
import com.google.mediapipe.formats.proto.LandmarkProto;
import com.google.mediapipe.framework.AndroidAssetUtil;
import com.google.mediapipe.framework.AndroidPacketCreator;
import com.google.mediapipe.framework.Packet;
import com.google.mediapipe.framework.PacketGetter;
import com.google.mediapipe.glutil.EglManager;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class MapControl extends AppCompatActivity {

    // 资源文件和流输出名
    private static final String BINARY_GRAPH_NAME = "hand_tracking_mobile_gpu.binarypb";
    private static final String INPUT_VIDEO_STREAM_NAME = "input_video";
    private static final String OUTPUT_VIDEO_STREAM_NAME = "output_video";
    private static final String OUTPUT_HAND_PRESENCE_STREAM_NAME = "hand_presence";
    private static final String OUTPUT_LANDMARKS_STREAM_NAME = "hand_landmarks";
    private static final String INPUT_NUM_HANDS_SIDE_PACKET_NAME = "num_hands";
    private static final int NUM_HANDS = 1;

    private SurfaceTexture previewFrameTexture;
    private SurfaceView previewDisplayView;
    private EglManager eglManager;
    private FrameProcessor processor;
    private ExternalTextureConverter converter;
    private CameraXPreviewHelper cameraHelper;

    private int next_song = 0;
    private int previous_song = 0;
    private int play_music = 0;
    private int pause_music = 0;

    long timestampbefor = -1;
    long timespend = 0;
    boolean flag = true;

    int k = 10;   //the number frame to do a act
    int numm = 0; //the total frame hand detection
    Float preVex = Float.valueOf(-1); // the prior hand x position
    Float handDistance = Float.valueOf(0);
    String currentView = "image_room";
    int songphotochangeflag=0;

    private static final int numThreads = 1;
    // 所使用的摄像头
    private static final boolean USE_FRONT_CAMERA = true;

    // 因为OpenGL表示图像时假设图像原点在左下角，而MediaPipe通常假设图像原点在左上角，所以要翻转
    private static final boolean FLIP_FRAMES_VERTICALLY = true;

    // 加载动态库
    static {
        System.loadLibrary("mediapipe_jni");
        System.loadLibrary("opencv_java3");
    }

    /**
     * 作为Handler toastHandler传递内容的函数，实现线程弹窗的显示
     * @param message1
     */
    private void send_message_to_bundle(String message1) {
        Bundle bundle = new Bundle();
        bundle.putString("action", message1);
        Message message = new Message();
        message.setData(bundle);
        toastHandler.sendMessage(message);
    }
    int flag_activity = 0;
    int finish_app = 0;
    private int array_to_count_activity[] = new int[20];
    //接听拒绝电话的处理
    private TelephonyManager tManager;
    private PhoneStateListener pListener;
    HashMap string_to_num_map = new HashMap();
    //静态手势识别模块
    int num_change_map=0;//服务于手势地图调节
    /*
    记录指尖点位轨迹
     */
    List<float[]>point_history=new ArrayList<>();//记录轨迹对应的点位坐标
    private int myInternal=5;//代表采样间隔的点位
    List<Float>point_catchX=new ArrayList<>();//记录采样处理之后的横坐标
    List<Float>point_catchY=new ArrayList<>();
    private Float base_x,base_y;//记录手腕基准点坐标
    private int upper_limit = 25;
    //记录地图移动过程中，前一个点的坐标
    private float prev_x=0;
    private float prev_y=0;
    //记录地图缩放过程中，前一个指尖的坐标，用来判断当前的处于地图的放大还是收缩过程中
    private float mapZoom_prev_x=0;
    private float mapZoom_prev_y=0;
    private int mapZoom_samePoint_times=0;//用来记录指尖同一个位置出现的次数  如果出现的次数较多，说明用户希望将地图保持在当前的缩放情况下
    //进入到地图移动的操作中，并暂停其余线程的操作
    /*
    flag_Mapcontrol用来控制获得手掌关键点之后进行地图控制的线程的选择
        return_pause作为地图相应手势操作模块识别完成下，进行暂停mediapipe手势识别的判断
     */
    private int flag_Mapcontrol=0;//默认状态下，仍然进行所有手势识别的操作
    private boolean return_pause=false;
    private int return_pause_num=0;//默认状态下，不需要暂停手势的识别
    /*
    调用窗口亮度调节的类，实现光线传感器对应的亮度自动调节
     */
    private BrightnessAdapter myAPP_BrightnessAdapter;

    /**
     * DTW状态确认的枚举类型
     */
    private enum EMode{
        // 当模型处于训练记录数据阶段
        TRAINING,
        // 当模型处于记录样本数据阶段
        RECORDING;
    }
//    private EMode mMode;// 设置模型对象 记录当前状态922

    /**
     * DTW 录入序列的手势选择
     */
    private enum Epose{
        // 选择地图放大手势的录入
        myzoomIn,
        // 选择地图缩小的手势录入
        myzoomOut;
    }
//    private Epose mPose;// 设置手势选择对象 923
//    private TextView mModeTitle;// 显示当前模型的状态 作为开关响应的一部分
//    private TextView mModeDescription; // 作为当前状态描述的一部分
//    private TextView mPoseDescription; // 作为手势选择描述的一部分
//    private Switch ModeSwitchforDTW;// DTW开关
//    private Switch PoseSwitchforDTW;// DTW姿势选择的开关
    private void HandleTheHands(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        Runtime runtime = Runtime.getRuntime();
        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
//        send_vedio_to_bundle("visible");
        // TODO: 8/30/2022 测试视频在没有继续输入的时候自动熄灭

//        Log.d(myTAG, "Mapcontrol当前输出的手势"+title);
        // 实现缩放手势保持一段时间地图缩放状态被固定
        if ("ChangeVol".equals(title)) {
            if(return_pause){
                if(return_pause_num==25) {
                    return_pause = false;//将当前的暂停判断恢复成默认状态
                    return_pause_num=0;
                }else{
                    return_pause_num++;
                    return;//将当前的手掌数据包舍弃
                }
            }
            /*
            处理第一次识别到手势
                记录下当前点位的坐标
                并且进入到地图缩放的识别中
             */
            // 标志进入到地图缩放的过程中
            flag_Mapcontrol=2;//进入到地图的缩放操作过程中
            // 获得关键点——拇指指尖的坐标
            float temp_x=landmarks.getLandmark(8).getX();
            float temp_y=landmarks.getLandmark(8).getY();
            //将得到的归一化的坐标按照图像的大小进行放大
            //当前得到的关键点的坐标只会被记录为初始位置的坐标，不会进入判断中
            mapZoom_prev_x=temp_x*image_width;
            mapZoom_prev_y=temp_y*image_height;
            //实现地图的缩放调节
//            if (flag_activity == -1 || flag_activity == 1) {
//                num_change_map++;
//            }
//            else
//            {
//                flag_activity = 1;
//                num_change_map = 0;
//            }
//            if (num_change_map == 20) {
//                //获取坐标数组
//                float[] landmark_list_temp = RecHands.getMultiHandLandmarksDebugXY(multiHandLandmarks);
//                //计算拇指和食指间的距离
//                Float Dis = RecHands.CalculDis(landmark_list_temp, 4, 8);
//                String myDis = Float.toString(Dis);
//                send_photo_to_bundle(myDis);
//                num_change_map = 0;
//                flag_activity = -1;
//            }
        }
//        SharedPreferences prefs = PreferenceManager.getDefaultSharedPreferences(this);//设置中对于当前控制手势类型的设置
//        String previous_song_option = prefs.getString("play_previous_song", "0");
//        if ("0".equals(previous_song_option)) {
//            string_to_num_map.put("handToLeft", 1);
//
//        } else if ("1".equals(previous_song_option)) {
//            string_to_num_map.put("one", 1);
//        }
//
//        String next_song_option = prefs.getString("play_next_song", "0");
//        if ("0".equals(next_song_option)) {
//            string_to_num_map.put("handToRight", 2);
//
//        } else if ("1".equals(next_song_option)) {
//            string_to_num_map.put("TWO", 2);
//        }
//
//        String stop_song_option = prefs.getString("stop_the_song", "0");
//        if ("0".equals(stop_song_option)) {
//            string_to_num_map.put("handStopMusic", 3);
//
//        } else if ("1".equals(stop_song_option)) {
//            string_to_num_map.put("fist", 3);
//        }
//
//        String play_song_option = prefs.getString("play_the_song", "0");
//        if ("0".equals(play_song_option)) {
//            string_to_num_map.put("OK", 4);
//
//        } else if ("1".equals(play_song_option)) {
//            string_to_num_map.put("THREE", 4);
//        }
        else if("Close2".equals(title))
        {
            /*
            处理第一次识别到手势
                记录下当前点位的坐标
                并且进入到地图拖拽的识别中
             */
            // 标志进入到地图拖拽识别的过程中
            flag_Mapcontrol=1;
            //获得关键点——中指指尖的坐标
            float temp_x=landmarks.getLandmark(12).getX();
            float temp_y=landmarks.getLandmark(12).getY();
            //将得到的归一化的坐标按照图像的大小进行放大
            prev_x=temp_x*image_width;
            prev_y=temp_y*image_height;
//            Log.d(myTAG, "当前对应的横坐标"+temp_x+"当前对应的纵坐标"+temp_y);// : 8/18/2022
//            //进入到手势轨迹获得和地图移动的操作中
//            myDragMap(multiHandLandmarks);
//            //当前图像中已经检测不到手掌的存在，退出地图的移动操作，进入其他操作中
//            prev_x=0;
//            prev_y=0;
//            //实现地图的上下移动情况
//            AMap aaMap=null;
//            if(aaMap==null){
//                aaMap=mMapView.getMap();//获得当前
//            }
//            /*
//            对于x y两个方向上阈值的判断，判定当前坐标的移动是否表示着地图的移动
//                纵坐标的阈值是5
//                横坐标的阈值是5
//             */
//            boolean flag_x=true;//默认是可以进行上下移动的
//            boolean flag_y=true;//默认是可以进行左右移动的
//            if(Math.abs(temp_x-prev_x)<5){
//                flag_x=false;
//            }
//            if(Math.abs(temp_y-prev_y)<5){
//                flag_y=false;
//            }
//            if(flag_x||flag_y){
//            /*
//            按照点位前后的相对移动距离，实现地图位置的移动
//             */
//                float map_x=0;
//                float map_y=0;
//                if(flag_x){
//                    map_x=temp_x-prev_x;
//                }
//                if(flag_y){
//                    map_y=temp_y-prev_y;
//                }
//                CameraPosition mCameraposition=null;
//                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
//                //其中 地图视角对应的缩放程度、俯仰程度保持相同
//                // 在修改地图对应的经纬度的时候，经度按照0.01进行修改，维度按照0.1进行修改
//                // 当前直接获得的手指坐标是
//                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude+map_y/10000,mCameraposition.target.longitude+map_x/10000),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
//                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
//            }
//            //记录当前点位的位置
//            prev_x=temp_x;
//            prev_y=temp_y;
//            // TODO: 8/19/2022 当前存在的问题：对于前一个点位位置的更新，在当前移动操作结束之后，仍然会保留上一个操作中点位的最终位置
        }
        else {
            string_to_num_map.put("FINISHSIGN", 0);//结束手势的设置
            string_to_num_map.put("SIX", 1);//接听手势的设置
            string_to_num_map.put("handStopMusic", 2);//拒绝电话的设置
            string_to_num_map.put("fist",3);//握拳进行重新定位
            string_to_num_map.put("Close2",4);//握拳进行重新定位
            if("Close2".equals(title)){
                Float x12=landmarks.getLandmark(12).getX();
                Float y12=landmarks.getLandmark(12).getY();
                /**
                 * 将mediapipe获得的坐标进行还原（按照图像大小）
                 */
                x12 = (float) min((int) (x12 * image_width), image_width - 1);// 存疑 这样得到的坐标不都是整数了嘛
                y12 = (float) min((int) (y12 * image_width), image_width - 1);
                float[] temp_arr1={x12,y12};
                point_history.add(temp_arr1);//记录中指指尖对应的坐标点
            }
            if (string_to_num_map.containsKey(title)) {
                int want_the_num = (Integer) string_to_num_map.get(title);
                if (flag_activity == -1 || flag_activity == want_the_num) {
                    array_to_count_activity[want_the_num]++;
                    change_the_bar(array_to_count_activity[want_the_num]);
                } else {
                    flag_activity = want_the_num;
                    array_to_count_activity[want_the_num] = 0;
                    change_the_bar(0);
                    // : 8/12/2022 在每次新触发轨迹记录的时候 需要对已有的序列进行清空
                    point_history.clear();
                }
                for (int i = 0; i < array_to_count_activity.length; i++) {
                    if (i == want_the_num)
                        continue;
                    array_to_count_activity[i] = 0;
                }
                if (array_to_count_activity[want_the_num] == upper_limit) {
//                    base_x=landmarks.getLandmark(0).getX();
//                    base_y=landmarks.getLandmark(0).getY();
                    doAction(want_the_num);
                }
            } else {
                for (int i = 0; i < array_to_count_activity.length; i++) {
                    array_to_count_activity[i] = 0;
                }
                change_the_bar(0);
                //整个计数器初始化的时候 同时对点记录的数组进行清空
                point_history.clear();
            }
        }
    }

    /**
     * 对于地图拖拽的动态手势的处理
     * @param multiHandLandmarks
     */
    private void myDragMap(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks)
    {
        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
        // 首先判断静态手势是否满足要求
        if(title.equals("Close2")){
            // 获得当前界面上的地图
            AMap aaMap=null;
            if(aaMap==null){
                aaMap=mMapView.getMap();//获得当前
            }
            // 获得关键点1中指指尖的坐标
            float temp_x=landmarks.getLandmark(8).getX();
            float temp_y=landmarks.getLandmark(8).getY();
            //将得到的归一化的坐标按照图像的大小进行放大
            temp_x=temp_x*image_width;
            temp_y=temp_y*image_height;
//            Log.d(myTAG, "myDragMap当前对应的横坐标"+temp_x+"当前对应的纵坐标"+temp_y);
            /*
            对于x y两个方向上阈值的判断，判定当前坐标的移动是否表示着地图的移动
                纵坐标的阈值是5
                横坐标的阈值是5
             */
            boolean flag_x=true;//默认是可以进行上下移动的
            boolean flag_y=true;//默认是可以进行左右移动的
            if(Math.abs(temp_x-prev_x)<5){
                flag_x=false;
            }
            if(Math.abs(temp_y-prev_y)<5){
                flag_y=false;
            }
//            Log.d(myTAG, "myDragMap判断当前竖直方向是否可以移动: "+flag_x+"判断当前水平方向是否可以移动:"+flag_y);
            if(flag_x||flag_y){
            /*
            按照点位前后的相对移动距离，实现地图位置的移动
             */
                float map_x=0;
                float map_y=0;
                if(flag_x){
                    map_x=-(temp_x-prev_x);
                }
                if(flag_y){
                    map_y=(temp_y-prev_y);//实现手指左滑，地图左移动
                }
                CameraPosition mCameraposition=null;
                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
                // 其中 地图视角对应的缩放程度、俯仰程度保持相同
                // 在修改地图对应的经纬度的时候，经度按照0.01进行修改，维度按照0.1进行修改
                // 当前直接获得的手指坐标是
                // TODO: 8/19/2022 地图移动的大小应当和地图缩放的大小成比例
                /*
                当前测试：zoom数值越大，地图越放大
                    标准情况下zoom对应的值是10
                 */
                //对地图缩放的数值进行量级的修改
                float zoom_now=mCameraposition.zoom;//记录当前地图视图对应的缩放程度的情况
                float zoom_standard=10;//记录默认状态下地图的缩放情况
                map_x=map_x/image_width;
                map_y=map_y/image_height;
                map_x= (float) (map_x/Math.pow(10,(zoom_now-zoom_standard)*0.25));
                map_y= (float) (map_y/Math.pow(10,(zoom_now-zoom_standard)*0.25));
                Log.d(myTAG, "myDragMap: 当前地图对应的缩放程度"+mCameraposition.zoom+"纬度:"+mCameraposition.target.latitude+"经度:"+mCameraposition.target.longitude);
//                Log.d(myTAG, "myDragMap:当前地图的缩放情况:"+mCameraposition.zoom+"当前经纬度移动的情况"+map_x+"经度移动的情况"+map_y);
                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude+map_y,mCameraposition.target.longitude+map_x),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
            }
            //记录当前点位的位置
            prev_x=temp_x;
            prev_y=temp_y;
            // TODO: 8/19/2022 当前存在的问题：对于前一个点位位置的更新，在当前移动操作结束之后，仍然会保留上一个操作中点位的最终位置
        }
        else{
            //当前手势不满足地图拖拽的操作
            flag_Mapcontrol=0;//重新退回到手势识别的过程中
        }
        }

    private List<MainMenu> fruitList = new ArrayList<>();
    Handler toastHandler;
    //弹出图像的处理
    Handler photoHandler;
    // 前置摄像头的视频流显示
    Handler vedioHandler;

    //手势识别的进度条
    ProgressBar progressBar;

    private void send_photo_to_bundle(String message1) //使用字符串控制活动
    {
        Bundle bundle = new Bundle();
        bundle.putString("photo", message1);
        Message message = new Message();
        message.setData(bundle);
        photoHandler.sendMessage(message);
    }

    /**
     * 作为召回的响应，不同线程实现前置摄像头显示的调用 8.30
     * @param message1
     */
    private void send_vedio_to_bundle(String message1) //使用字符串控制活动
    {
        Bundle bundle = new Bundle();
        bundle.putString("vedio", message1);
        Message message = new Message();
        message.setData(bundle);
        vedioHandler.sendMessage(message);
    }

    //照片的修改
    ImageView handimg;
    float prevDis=0;
    private void changeSongsphoto(String myDis)
    {
        float dis=Float.parseFloat(myDis);
        if(dis>15)
            dis=15;
        Log.d("myTAG", "前一个手势的距离："+prevDis+" 后一个手势的距离："+dis);
        if(dis>prevDis+0.45)//放大的判断条件：当前手指间距比前一个状态大0.45情况下触发
        {
//            手指间距处于放大趋势
//            upphotoTimes++;
            changemapphoto(1);//图片放大
            prevDis=dis;
        }
        else if(dis<prevDis-0.5)
        {
            //手指间距处于缩小趋势
//            lowphotoTimes++;
            changemapphoto(0);//图片缩小
            prevDis=dis;
        }
        else if(dis==prevDis)
        {
            return;//不需要进行处理
        }
//        int staThumb=15;
//        handimg=findViewById(R.id.map_photo);
//        Bitmap bitmap= BitmapFactory.decodeResource(getResources(),R.drawable.maptest);
//        Log.d("79map", "dis: "+dis);
//        double size=dis/staThumb;
//        size=1-size;//7.13 手势在快速切换图片的大小的时候 容易导致app闪退
//        if(size<=0.05)
//            size=0.05;
//        else if(size>=1.8)//注意不能太大 会出现too large Bitmap的报错
//            size=1.8;
//        7.13封存
//        Log.d("79map", "currsize: "+size);
//        int bitmapHeight = bitmap.getHeight();
//        int bitmapWidth = bitmap.getWidth();
//        Log.d("79map", "照片原本的长和宽: "+bitmapHeight+" "+bitmapWidth);
//        int tempbitmapHeight=max(1,(int) (bitmapHeight*size));
//        int tempbitmapWidth=max(1,(int)(bitmapWidth*size));
//        bitmapHeight=min(bitmapHeight,tempbitmapHeight);
//        bitmapWidth=min(bitmapWidth,tempbitmapWidth);
//        Matrix matrix=new Matrix();
//        matrix.postScale((float) size,(float) size);
//        Bitmap temp=Bitmap.createBitmap(bitmap,0,0,bitmapWidth,bitmapHeight,matrix,true);
//        handimg.setImageBitmap(temp);
//        temp=null;
//        Log.d("79map", "照片的长和宽: "+bitmapHeight+" "+bitmapWidth);
    }

//    使用按钮实现对地图缩放的控制
//    //使用照片进行测试的情况
    //upphotoTimes和lowphotoTimes用来判断当前放大和缩小的次数
//    private int upphotoTimes=0,lowphotoTimes=0,prevbitmapHeight=3864,prevbitmapWidth=2500;//prev的长和高用照片对应的长和高进行初始化
//    private void changemapphoto(int flag)
//    {
//        handimg=findViewById(R.id.map_photo);
//        Bitmap bitmap= BitmapFactory.decodeResource(getResources(),R.drawable.maptest);
//        int bitmapHeight = bitmap.getHeight();//注意获得的是 当前展示所在的窗口的大小 而不是照片的大小
//        int bitmapWidth = bitmap.getWidth();
//        double size;
//        if(flag==1)//图片放大
//        {
//            size=1-0.05*upphotoTimes;
//            bitmapHeight=max(1,(int)(prevbitmapHeight*size));//如果当前图片的长或宽出现0的情况就会引发闪退的出现
//            bitmapWidth=max(1,(int)(prevbitmapWidth*size));
//            lowphotoTimes=0;
//        }
//        else if(flag==0)//图片缩小
//        {
//            size=max(0.000001,1+0.05*lowphotoTimes);
//            bitmapHeight=(int)(prevbitmapHeight*size);
//            bitmapWidth=(int)(prevbitmapWidth*size);
//            upphotoTimes=0;
//        }
//        Log.d("713map", "当前长和宽: "+bitmapHeight+" "+bitmapWidth);
//        bitmapHeight=min(bitmap.getHeight(),bitmapHeight);//限制不要超过原始照片的大小
//        bitmapWidth=min(bitmap.getWidth(),bitmapWidth);
//        prevbitmapHeight=bitmapHeight;
//        prevbitmapWidth=bitmapWidth;
//        Matrix matrix=new Matrix();
//        if(flag==1)
//            matrix.postScale((float) 0.95,(float) 0.95);
//        else
//            matrix.postScale((float) 1.05,(float) 1.05);
//        Bitmap temp=Bitmap.createBitmap(bitmap,0,0,bitmapWidth,bitmapHeight,matrix,true);
//        handimg.setImageBitmap(temp);
//        temp=null;
//    }

    /**
     * 前置摄像头视频显示回调的响应函数，控制视频的显示与否
     * @param action
     */
    public void videoVisible(String action){
        TextView myFrontVideo=findViewById(R.id.no_camera_access_view2);
        long startTime=0,nowTime=0;
        boolean flag=false;
        if(action.equals("visible")){
            myFrontVideo.setVisibility(View.VISIBLE);
            startTime=System.currentTimeMillis();
            flag=true;
        }
        while(flag){
            nowTime=System.currentTimeMillis();
            if (nowTime-startTime==200){
                // 显示2秒后自动消失
                myFrontVideo.setVisibility(View.INVISIBLE);
                flag=false;
                // TODO: 8/30/2022 测试视频在没有继续输入的时候自动熄灭
            }
        }
    }
    /**
     * 控制地图的缩放
     * @param flag
     */
    private void changemapphoto(int flag){
        if(flag==0){//图片缩小
            //声明控制地图情况的局部变量
            AMap aaMap=null;
            if(aaMap==null){
                aaMap=mMapView.getMap();//获得当前在onCreate创建的地图画布
            }
            aaMap.moveCamera(CameraUpdateFactory.zoomOut());//调用函数 将地图当前的视角进行缩小
        }else if(flag==1){//图片放大
            //声明控制地图情况的局部变量
            AMap aaMap=null;
            if(aaMap==null){
                aaMap=mMapView.getMap();//获得当前在onCreate创建的地图画布
            }
            aaMap.moveCamera(CameraUpdateFactory.zoomIn());//调用函数 将地图当前的视角进行放大
        }
    }


    MapView mMapView = null;
    //用于地图的定位
    public AMapLocationClient mLocationClient = null;
    //声明定位回调监听器
    public AMapLocationListener mAMapLocationListener = new AMapLocationListener(){
        /*
        定位成功之后的回调函数
         */
        @Override
        public void onLocationChanged(AMapLocation amapLocation) {
            //解析AMapLocation对象
            //首先需要对AMapLocation判空，当定位错误码类型为0时候表示定位成功
            if(amapLocation!=null){
                if(amapLocation.getErrorCode()==0){//当定位成功的时候
                    //可以对amapLocation中的内容进行解析
                }else{
                    //当定位失败的时候，选择ErrCode错误码信息确定失败的原因，errInfo是错误的信息
                    Log.e("AmapError", "location Error, ErrCode:"
                            + amapLocation.getErrorCode() + ", errInfo:"
                            + amapLocation.getErrorInfo());
                }
            }
        }
    };
    public AMapLocationClientOption mLocationOption = null;
    private Date date;
    private long pauseStartTime=0;
    private long pauseEndTime=0;

    @Override
    protected void onCreate(Bundle savedInstanceState) {

        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_map_control1);
        initFruits();
        MenuAdapter adapter = new MenuAdapter(this, R.layout.main_menu_ui_item, fruitList);
        ListView listView = (ListView) findViewById(R.id.list_view_music);
        listView.setAdapter(adapter);
        //对于listview中点击事件添加
        listView.setOnItemClickListener(new AdapterView.OnItemClickListener() {
            @Override
            public void onItemClick(AdapterView<?> parent, View view, int position, long id) {
                switch (position) {
                    case 0:
//                        Toast.makeText(MapControl.this,"第"+position+"个item", Toast.LENGTH_SHORT).show();
                    {
//                        upphotoTimes++;
                        changemapphoto(1);//照片放大
                        break;
                    }
                    case 1:
                    {
//                        lowphotoTimes++;
                        changemapphoto(0);//照片缩小
                        break;
                    }
                    case 2:
//                        Toast.makeText(MapControl.this,"接听电话", Toast.LENGTH_SHORT).show();
                        doAction(1);
                        break;
                    case 3:
//                        Toast.makeText(MapControl.this,"拒绝电话", Toast.LENGTH_SHORT).show();
                        doAction(2);
                        break;
                    case 4:
//                        Toast.makeText(MapControl.this,"退出", Toast.LENGTH_SHORT).show();
                        finish();
                        break;
                }
            }
        });
        next_song = 0;
        previous_song = 0;

        date=new Date();
//        // 922 DTW默认状态设定为识别记录状态
//        mMode=EMode.RECORDING;
//        // DTW默认状态设定为地图放大手势的选择
//        mPose=Epose.myzoomIn;
        // DTW数据记录和训练记录数据的切换开关 920
//        ModeSwitchforDTW=findViewById(R.id.mode_switch);
//        PoseSwitchforDTW=findViewById(R.id.pose_switch);
//        mModeTitle=findViewById(R.id.tv_mode);// 描述当前模型的状态
//        mModeDescription=findViewById(R.id.tv_mode_desc);// 当前状态操作的描述
//        mPoseDescription=findViewById(R.id.tv_pose_desc);// 找到对应的textview
        /*
        设置数据记录开关对应的响应情况
         */
//        ModeSwitchforDTW.setOnCheckedChangeListener(new CompoundButton.OnCheckedChangeListener() {
//            @Override
//            public void onCheckedChanged(final CompoundButton compoundButton, final boolean b) {
//                // 更新当前模型的状态 开关打开状态是训练状态——只记录数据
//                mMode=(b?EMode.TRAINING:EMode.RECORDING);
//                // 描述的textview的修改
//                mModeTitle.setText(b?"Training Mode训练状态":"Recording Mode记录状态");
//                mModeDescription.setText(b?"做出地图缩放手势作为模板":"做出缩放手势进行地图缩放操作");
//                if(mMode==EMode.TRAINING) {
//                    if(mPose==Epose.myzoomIn){
//                        // 选择地图放大手势
//                        // 每次记录训练数据时均需要对序列进行清空
//                        num3.trainingHistory[0].clear();
//                        num3.trainingHistory[1].clear();
//                        num4.trainingHistory[0].clear();
//                        num4.trainingHistory[1].clear();
//                        num6.trainingHistory[0].clear();
//                        num6.trainingHistory[1].clear();
//                        num7.trainingHistory[0].clear();
//                        num7.trainingHistory[1].clear();
//                        num8.trainingHistory[0].clear();
//                        num8.trainingHistory[1].clear();
//                    }else if(mPose==Epose.myzoomOut){
//                        // 选择地图缩小的手势进行训练
//                        // 每次记录训练数据时均需要对序列进行清空
//                        num30.trainingHistory[0].clear();
//                        num30.trainingHistory[1].clear();
//                        num40.trainingHistory[0].clear();
//                        num40.trainingHistory[1].clear();
//                        num60.trainingHistory[0].clear();
//                        num60.trainingHistory[1].clear();
//                        num70.trainingHistory[0].clear();
//                        num70.trainingHistory[1].clear();
//                        num80.trainingHistory[0].clear();
//                        num80.trainingHistory[1].clear();
//                    }
//                }
//                else if(mMode==EMode.RECORDING){
//                    if(mPose==Epose.myzoomOut){
//                        Log.d(myTAG, String.format("当前切换成记录状态，训练缩小手势序列记录的数据长度是:%d",num40.trainingHistory[0].size()));
//                    }else if(mPose==Epose.myzoomIn){
//                        Log.d(myTAG, String.format("当前切换成记录状态，训练放大手势序列记录的数据长度是:%d",num4.trainingHistory[0].size()));
//                    }
//                }
//            }
//        });
        // DTW手势切换的响应
//        PoseSwitchforDTW.setOnCheckedChangeListener(new CompoundButton.OnCheckedChangeListener() {
//            @Override
//            public void onCheckedChanged(CompoundButton compoundButton, boolean b) {
//                // 更新当前模型的状态 开关打开状态是选择地图缩小手势
//                mPose=(b?Epose.myzoomIn:Epose.myzoomOut);
//                // 描述的textview的修改
//                mPoseDescription.setText(b?"选择地图放大手势":"选择地图缩小手势");
//            }
//        });
         /*
        使用光线传感器实现亮度的调节
        8.20 成功
         */
        myAPP_BrightnessAdapter =new BrightnessAdapter(getApplicationContext(),getWindow());
        myAPP_BrightnessAdapter.regist();

        /*
        重点 地图的构建部分 具体的注释请参考Maptest0部分的代码
         */
        //地图的隐私检查 需要在地图创建之前完成
        MapsInitializer.updatePrivacyShow(this, true, true);//隐私合规状态
        MapsInitializer.updatePrivacyAgree(this,true);//更新同意隐私状态
        //获得地图控件
        mMapView=(MapView)findViewById(R.id.map);
        //创建地图
        mMapView.onCreate(savedInstanceState);
        /*
        地图显示的实现
         */
        //初始化地图控制器对象
        AMap aMap = null;
        if (aMap == null) {
            aMap = mMapView.getMap();
        }
        //地图定位
        try {
            mLocationClient = new AMapLocationClient(getApplicationContext());
        } catch (Exception e) {
            e.printStackTrace();
        }
        //定位回调监听
        mLocationClient.setLocationListener(mAMapLocationListener);//设置对应的监听器
        //配置参数并启动定位
        mLocationOption=new AMapLocationClientOption();
        //定位模式的选择 目前选择的是高精度模式
        mLocationOption.setLocationMode(AMapLocationClientOption.AMapLocationMode.Battery_Saving);

        //定位蓝点的配置
        MyLocationStyle myLocationStyle;
        myLocationStyle=new MyLocationStyle();//初始化定位蓝点样式
        myLocationStyle.interval(2000);//设置连续定位模式下的定位间隔
        myLocationStyle.myLocationType(MyLocationStyle.LOCATION_TYPE_FOLLOW);//定位时蓝点不随手机移动
        aMap.setMyLocationStyle(myLocationStyle);//设置定位的格式
//        aMap.getUiSettings().setMyLocationButtonEnabled(true);//设置自带的定位按钮显示
//        aMap.setMyLocationEnabled(true);//设置启动显示定位蓝点并定位(onCreate启动时候实现自动定位)
        //设置定位的小蓝点是否显示
        myLocationStyle.showMyLocation(true);
        // 设置定位监听
//        aMap.setLocationSource((LocationSource) this);
        //设置为true表示启动显示定位蓝点，false表示隐藏定位蓝点并不进行定位，默认是false。
        aMap.setMyLocationEnabled(true);
        Log.d(myTAG, "开始定位: ");
        // 设置地图模式，aMap是地图控制器对象。1.MAP_TYPE_NAVI:导航地图 2.MAP_TYPE_NIGHT:夜景地图 3.MAP_TYPE_NORMAL:白昼地图（即普通地图） 4.MAP_TYPE_SATELLITE:卫星图
        aMap.setMapType(AMap.MAP_TYPE_SATELLITE);

        //地图变化监视器--实现在点按按钮后自动撤销定位 重新点按按钮后再次定位 修改 没有明确定位的生命周期 导致整个定位系统耗时过长
        aMap.setOnCameraChangeListener(new AMap.OnCameraChangeListener() {
            @Override
            public void onCameraChange(CameraPosition cameraPosition) {

            }

            @Override
            public void onCameraChangeFinish(CameraPosition cameraPosition) {//地图发生变化之后
                //声明控制地图的局部变量
                AMap aaMap=null;
                if(aaMap==null){
                    aaMap=mMapView.getMap();//获得当前的地图画布
                }
                // TODO: 7/29/2022
                aaMap.setMyLocationEnabled(false);//关闭定位 修改 实际上是将定位情况在地图中隐藏不见 修改为：添加地图定位生命周期的结束 之后在对应的定位模块再添加定位的生命周期
                Log.d(myTAG, "隐藏地图定位: ");
            }
        });

        previewDisplayView = new SurfaceView(this);
        setupPreviewDisplayView();
        // 获取权限
        PermissionHelper.checkAndRequestCameraPermissions(this);

        // 初始化assets管理器，以便MediaPipe应用资源
        AndroidAssetUtil.initializeNativeAssetManager(this);

        eglManager = new EglManager(null);

        // 通过加载获取一个帧处理器
        processor = new FrameProcessor(
                this,
                eglManager.getNativeContext(),
                BINARY_GRAPH_NAME,
                INPUT_VIDEO_STREAM_NAME,
                OUTPUT_VIDEO_STREAM_NAME);
        processor.getVideoSurfaceOutput().setFlipY(FLIP_FRAMES_VERTICALLY);


        AndroidPacketCreator packetCreator = processor.getPacketCreator();
        Map<String, Packet> inputSidePackets = new HashMap<>();
        inputSidePackets.put(INPUT_NUM_HANDS_SIDE_PACKET_NAME, packetCreator.createInt32(NUM_HANDS));
        processor.setInputSidePackets(inputSidePackets);

        toastHandler=new Handler(new Handler.Callback() {
            @Override
            public boolean handleMessage(@NonNull Message msg) {
                Bundle bundle=msg.getData();
                //获得当前的动作
                String action=(String)bundle.get("action");
                //执行动作，实现文字的弹窗实现
                textPopToast(action);
                return false;
            }
        });
        photoHandler = new Handler(new Handler.Callback() {
            @Override//对于进行手势的识别
            public boolean handleMessage(Message msg) {
                Bundle bundle = msg.getData();
                //获取当前动作 也就是每个Handler传递的文字内容
                String action = (String) bundle.get("photo");
                //执行动作 照片的弹窗
                changeSongsphoto(action);
                return false;
            }
        });
        vedioHandler=new Handler(new Handler.Callback() {
            @Override
            public boolean handleMessage(@NonNull Message msg) {
                Bundle bundle=msg.getData();
                //获得当前的动作
                String action=(String)bundle.get("vedio");
                //执行动作，实现摄像头视频流的显示
                videoVisible(action);
                return false;
            }
        });

//        Log.d("indexof", "test");

        //调节进度条
        progressBar = (ProgressBar) findViewById(R.id.progress_bar_music);
        change_the_bar(0);


        ansdenyPhone();


        //新增一个识别手指，并进行操作的模块
        processor.addPacketCallback(
                OUTPUT_LANDMARKS_STREAM_NAME,
                (packet) -> {
                    List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks =
                            PacketGetter.getProtoVector(packet, LandmarkProto.NormalizedLandmarkList.parser());//添加不断获得对应关键点坐标的线程
                    /*
                        如果判定位当前处于地图操作完成的返回过程中，需要将一定数量的手掌数据包舍弃
                     */
//                    if(return_pause){
//                        // 获得当前数据包对应的时间
//                        pauseEndTime=date.getSeconds();
//                        Log.d(myTAG, "开始时间:"+pauseStartTime+" 结束时间："+pauseEndTime+" 时间差:"+(pauseEndTime-pauseStartTime));
//                        if(return_pause_num==50) {
//                            return_pause = false;//将当前的暂停判断恢复成默认状态
//                            return_pause_num=0;
//                        }else{
//                            return_pause_num++;
//                            return;//将当前的手掌数据包舍弃
//                        }
//                    }
                    if(return_pause){
                        // 获得当前数据包对应的时间
                        pauseEndTime=packet.getTimestamp();
                        Log.d(myTAG, "开始时间:"+pauseStartTime+" 结束时间："+pauseEndTime+" 时间差:"+(pauseEndTime-pauseStartTime));
                        if(pauseEndTime-pauseStartTime>=2000000) {
                            pauseEndTime=0;
                            pauseStartTime=0;
                            return_pause = false;//将当前的暂停判断恢复成默认状态
//                            return_pause_num=0;
                        }else{
//                            return_pause_num++;
                            return;//将当前的手掌数据包舍弃
                        }
                    }
                    // : 8/19/2022 测试 当进行地图拖拽的时候，其余手势的识别同步暂停
                    if(flag_Mapcontrol==0){
//                        Log.d(myTAG, "onCreate: flag_Mapdrag"+flag_Mapdrag);
                        HandleTheHands(multiHandLandmarks);//手势识别的线程
                    }
                    if (flag_Mapcontrol==1){
                        // 处理地图拖拽的动态手势
//                        Log.d(myTAG, "onCreate: 当前进行地图拖拽的操作"+flag_Mapdrag);
                        myDragMap(multiHandLandmarks);
                    }
                    if(flag_Mapcontrol==2){
                        // 处理地图缩放的动态手势
                        myZoommap(packet,multiHandLandmarks);// 传参packet是因为需要获得数据包的时间
                    }
//                    HandleTheMap(multiHandLandmarks);
//                    if (juTheback(packet, multiHandLandmarks)) {
//                        finish();
//                    }
                }
        );
    }

    /**
     * 用来处理文字弹窗的情况
     * @param action 作为弹窗需要显示的内容
     */
    private void textPopToast(String action) {
        Log.d(myTAG, "textPopToast: 当前action中的内容"+action);
        Toast toast=Toast.makeText(getApplicationContext(),action,Toast.LENGTH_SHORT);
        toast.show();
    }

//    private void myZoommap(Packet packet, List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks)    {
//        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);
//        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
//        if(title.equals("ChangeVol")){
//            //实现地图的上下移动情况
//            AMap aaMap=null;
//            if(aaMap==null){
//                aaMap=mMapView.getMap();//获得当前
//            }
//            //获得关键点——中指指尖的坐标
//            float temp_x=landmarks.getLandmark(8).getX();
//            float temp_y=landmarks.getLandmark(8).getY();
//            //将得到的归一化的坐标按照图像的大小进行放大
//            temp_x=temp_x*image_width;
//            temp_y=temp_y*image_height;
////            Log.d(myTAG, "myDragMap当前对应的横坐标"+temp_x+"当前对应的纵坐标"+temp_y);
//            /*
//            对于手指方向的判断
//                如果手指处于扩展的趋势，地图进行放大
//                如果手指处于收缩的趋势，地图进行缩小
//             */
//            int flag_zoom=0;//默认是进行地图的放大
//            float dis_y=-(temp_y-mapZoom_prev_y);// 计算前后坐标的变化
//            /*
//                判断手指是否在移动的过程中
//                    如果手指保持在一个位置，表示用户需要将地图的大小保持在这个位置
//                    因此需要将变化范围在一个阈值内的情况过滤出来，不进行地图的缩放
//                记录指尖在同一个位置出现的次数 mapZoom_samePoint_times
//                    如果指尖多次重复在同一个位置出现，表示用户当前不希望更改当前地图的缩放程度
//             */
//            if(Math.abs(dis_y)<=10){
//                mapZoom_samePoint_times++;
//                Log.d(myTAG, "myZoommap: 当前指尖位置被识别的次数:"+mapZoom_samePoint_times);
//                /*
//                如果指尖在同一个位置进行了多次保存，需要提示用户当前地图的缩放操作已经停止，进入到其余手势的识别中
//                 */
//                if(mapZoom_samePoint_times==20){
//                    // 当手指在相同位置保持了20次
////                    Toast.makeText(this,"当前地图缩放已经定位",Toast.LENGTH_SHORT).show();
//                    send_message_to_bundle("当前地图的缩放已经定位，进入到其余手势的识别过程中");
//                    return_pause=true;//将mediapipe手势识别的线程暂停
//                    pauseStartTime=packet.getTimestamp();// 获得当前数据包的时间
//                    pauseEndTime=0;
//                    /*
//                        注意，当前对于缩放手势的判断属于一个单独的线程，在当前线程暂停（使用thread.sleep仅仅是将当前的线程暂停）
//                        但是上面获得关键点坐标的线程仍然处于运行的状态中
//                        因此，会出现当前线程解决后，暂停过程中关键点的坐标仍然被保留，并且线程结束暂停后继续被处理
//                     */
//                    Log.d(myTAG, "myZoommap: 当前地图的缩放已经定位，进入到其余手势的识别过程中");
//                    num_change_map=0;
//                    flag_Mapcontrol=0;//进入到其余手势的识别中,并且作为
////                    try {
////                        Thread.sleep(3000);//当前的线程睡眠1s
////                    }catch (Exception e){}
//                }
//                return;//当前变化的范围过小，不属于地图缩放的范围
//            }
//            mapZoom_samePoint_times=0;//当指尖从新的位置离开的时候，次数需要更新
//            //获得地图当前显示的位置情况
//            CameraPosition mCameraposition=null;
//            mCameraposition=aaMap.getCameraPosition();
//            CameraUpdate mCameraUpdate=null;
//            /*
//            按照点位前后的相对移动距离，实现地图视角的缩放
//                其中 地图视角对应的经度和维度、俯仰程度保持相同
//                当前测试：zoom数值越大，地图越放大
//                标准情况下zoom对应的值是10
//             */
//            //当前地图的缩放情况
//            float map_zoom_now=mCameraposition.zoom;
//            Log.d(myTAG, "myZoommap: 当前手指移动的距离"+dis_y);
//
//            dis_y=dis_y/image_height;//进行标准化
//            dis_y=dis_y*100;
//
//            mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude,mCameraposition.target.longitude),map_zoom_now+dis_y,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
//            aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
//            //当前点位位置更新为前一个点位
//            mapZoom_prev_x=temp_x;
//            mapZoom_prev_y=temp_y;
//        }
//        else{
//            //当前手势不满足地图拖拽的操作
//            flag_Mapcontrol=0;//重新退回到手势识别的过程中
//        }
//    }

    // : 9/10/2022 按照手势关键点坐标的情况实现
    private float MapZoom_prev_finger_dist=0;// 记录上一次缩放手势手指之间的距离
    private long packet_prevTime=0;// 记录上一个数据包的时间
    /**
     * 处理地图缩放的动态手势
     * @param packet
     * @param multiHandLandmarks
     */
    private void myZoommap(Packet packet, List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks)    {
        double treshhold=0.25;// 设置DTW算法判断两个序列相同与否的阈值
        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
        // 获取当前的地图
        // 声明控制地图情况的局部变量
        AMap aaMap=null;
        if(aaMap==null){
            aaMap=mMapView.getMap();//获得当前在onCreate创建的地图画布
        }

        pauseStartTime=packet.getTimestamp();// 获得当前数据包的时间
//        Log.d(myTAG, "当前数据包时间："+pauseStartTime+" 之前数据包时间:"+packet_prevTime+" 数据包时间上的差值:"+(pauseStartTime-packet_prevTime));
        /*
        首先对数据进行间隔取样
         */
        if(pauseStartTime-packet_prevTime<=120000){
            // 当数据包的时间差在120000以内将数据包舍弃，也就是两个数据包的间隔，再对手势做出响应
            return;
        }else{
            // 数据包指尖的时间间隔满足要求，对记录的数据包的时间进行更新
            packet_prevTime=pauseStartTime;
        }

        // 首先判断静态手势是否满足
        if(title.equals("ChangeVol")){
            // 创建地图变量获得当前界面上的地图
            if(aaMap==null){
                aaMap=mMapView.getMap();
            }
            //获得关键点——当前每个手指各选择指尖坐标进行判断
            float temp_x8=landmarks.getLandmark(8).getX();
            float temp_y8=landmarks.getLandmark(8).getY();
            float temp_x7=landmarks.getLandmark(7).getX();
            float temp_y7=landmarks.getLandmark(7).getY();
            float temp_x6=landmarks.getLandmark(6).getX();
            float temp_y6=landmarks.getLandmark(6).getY();
            float temp_x4=landmarks.getLandmark(4).getX();
            float temp_y4=landmarks.getLandmark(4).getY();
            float temp_x3=landmarks.getLandmark(3).getX();
            float temp_y3=landmarks.getLandmark(3).getY();
            //将得到的归一化的坐标按照图像的大小进行放大
//            temp_x8=temp_x8*image_width;
//            temp_y8=temp_y8*image_height;
//            temp_x7=temp_x7*image_width;
//            temp_y7=temp_y7*image_height;
//            temp_x6=temp_x6*image_width;
//            temp_y6=temp_y6*image_height;
//            temp_x4=temp_x4*image_width;
//            temp_y4=temp_y4*image_height;
//            temp_x3=temp_x3*image_width;
//            temp_y3=temp_y3*image_height;

            // 对模型状态进行判断
//            if(mMode==EMode.TRAINING){
//                // Log.d(myTAG, "当前属于训练数据的收集中");
//
//                // 处于训练状态 将序列进行记录 当前序列的默认长度是100 当用户切换开关，序列记录暂停，打印对应序列长度
//                // 查看当前手势选择
//                if(mPose==Epose.myzoomOut){
//                    // 选择的是地图缩小手势
////                    num30.trainingHistory[0].add(temp_x3);
////                    num30.trainingHistory[1].add(temp_y3);
//                    num40.trainingHistory[0].add(temp_x4);
//                    num40.trainingHistory[1].add(temp_y4);
////                    num60.trainingHistory[0].add(temp_x6);
////                    num60.trainingHistory[1].add(temp_y6);
////                    num70.trainingHistory[0].add(temp_x7);
////                    num70.trainingHistory[1].add(temp_y7);
//                    num80.trainingHistory[0].add(temp_x8);
//                    num80.trainingHistory[1].add(temp_y8);
//                }else if(mPose==Epose.myzoomIn){
//                    // 选择的是地图放大的手势
////                    num3.trainingHistory[0].add(temp_x3);
////                    num3.trainingHistory[1].add(temp_y3);
//                    num4.trainingHistory[0].add(temp_x4);
//                    num4.trainingHistory[1].add(temp_y4);
////                    num6.trainingHistory[0].add(temp_x6);
////                    num6.trainingHistory[1].add(temp_y6);
////                    num7.trainingHistory[0].add(temp_x7);
////                    num7.trainingHistory[1].add(temp_y7);
//                    num8.trainingHistory[0].add(temp_x8);
//                    num8.trainingHistory[1].add(temp_y8);
//                }
//            }else if(mMode==EMode.RECORDING){
//                // Log.d(myTAG, "当前处于手势识别序列的收集中");
//                // 处于记录状态 按照训练数据的长度收集序列
//
//                // 判断记录序列收集长度是否达到要求
//                    // 当记录序列的长度短于训练模板序列的长度
////                    num3.recordingHistor[0].add(temp_x3);
////                    num3.recordingHistor[1].add(temp_y3);
//                    num4.recordingHistor[0].add(temp_x4);
//                    num4.recordingHistor[1].add(temp_y4);
////                    num6.recordingHistor[0].add(temp_x6);
////                    num6.recordingHistor[1].add(temp_y6);
////                    num7.recordingHistor[0].add(temp_x7);
////                    num7.recordingHistor[1].add(temp_y7);
//                    num8.recordingHistor[0].add(temp_x8);
//                    num8.recordingHistor[1].add(temp_y8);
//                    // 地图缩小的手势
////                    num30.recordingHistor[0].add(temp_x3);
////                    num30.recordingHistor[1].add(temp_y3);
//                    num40.recordingHistor[0].add(temp_x4);
//                    num40.recordingHistor[1].add(temp_y4);
////                    num60.recordingHistor[0].add(temp_x6);
////                    num60.recordingHistor[1].add(temp_y6);
////                    num70.recordingHistor[0].add(temp_x7);
////                    num70.recordingHistor[1].add(temp_y7);
//                    num80.recordingHistor[0].add(temp_x8);
//                    num80.recordingHistor[1].add(temp_y8);
//                int lt=num4.trainingHistory[0].size();
//                int lr=num4.recordingHistor[0].size();// 地图放大手势
//                if(lr>=lt+2){
//                    Log.d(myTAG, "当前地图放大手势识别序列的长度:"+num4.recordingHistor[0].size());
//                    // 当记录序列的长度达到模板序列长度的要求(当前设置超出原始序列长度2个) 选择使用DTW计算两个序列的相似度
//                    /*
//                     根据手势的特点，地图放大手势常常调用当前部分
//                     并且根据实验得到的阈值，识别的距离在0.3到0.5范围内
//                     */
//                    // 创建DTW算法的类
//                    final DTW lDTW= new DTW();
//                    // 记录DTW计算的结果 并且包含两个维度的结果
//                    List<Double>[]ans=new List[]{new ArrayList(),new ArrayList()};
//                    // 数据的预处理 转换成以序列第一个点为原点的坐标(使用坐标的相对位置关系)
////                    myPreview(num3.recordingHistor[0]);
////                    myPreview(num3.recordingHistor[1]);
//                    myPreview(num4.recordingHistor[0]);
//                    myPreview(num4.recordingHistor[1]);
////                    myPreview(num6.recordingHistor[0]);
////                    myPreview(num6.recordingHistor[1]);
////                    myPreview(num7.recordingHistor[0]);
////                    myPreview(num7.recordingHistor[1]);
//                    myPreview(num8.recordingHistor[0]);
//                    myPreview(num8.recordingHistor[1]);
//                    // 对每个点的两个坐标计算
////                    ans[0].add(lDTW.compute(primitive(num3.recordingHistor[0]),primitive(num3.trainingHistory[0])).getDistance());// x
////                    ans[1].add(lDTW.compute(primitive(num3.recordingHistor[1]),primitive(num3.trainingHistory[1])).getDistance());// y
//                    ans[0].add(lDTW.compute(primitive(num4.recordingHistor[0]),primitive(num4.trainingHistory[0])).getDistance());// x
//                    ans[1].add(lDTW.compute(primitive(num4.recordingHistor[1]),primitive(num4.trainingHistory[1])).getDistance());// y
////                    ans[0].add(lDTW.compute(primitive(num6.recordingHistor[0]),primitive(num6.trainingHistory[0])).getDistance());// x
////                    ans[1].add(lDTW.compute(primitive(num6.recordingHistor[1]),primitive(num6.trainingHistory[1])).getDistance());// y
////                    ans[0].add(lDTW.compute(primitive(num7.recordingHistor[0]),primitive(num7.trainingHistory[0])).getDistance());// x
////                    ans[1].add(lDTW.compute(primitive(num7.recordingHistor[1]),primitive(num7.trainingHistory[1])).getDistance());// y
//                    ans[0].add(lDTW.compute(primitive(num8.recordingHistor[0]),primitive(num8.trainingHistory[0])).getDistance());// x
//                    ans[1].add(lDTW.compute(primitive(num8.recordingHistor[1]),primitive(num8.trainingHistory[1])).getDistance());// y
//                    // 根据计算的结果判断分类情况
//                    int n_keypoints=2;// 设定的关键点的数量
//                    double[]ans_average=new double[n_keypoints];
//                    double ans_sum=0,ans_totalAver;
//                    // 设定按照x y两个方向上距离的平均值进行衡量
//                    for(int i=0;i<n_keypoints;i++){
//                        ans_average[i]=(ans[0].get(i)+ans[1].get(i))/2;
//                        ans_sum+=ans_average[i];
//                    }
//                    ans_totalAver=ans_sum/n_keypoints;// 计算所有关键点的平均相似度
//                    /*
//                    DTW手势分类阈值的修改
//                     */
//                    if(ans_totalAver>0.2){
//                        // 当前阈值的设置：通过实验测试得到
////                        Log.d(myTAG, (String.format("当前计算结果(相似度的平均值):\nnum3:%f num4:%f num6:%f num7:%f num8:%f\n",ans_average[0],ans_average[1],ans_average[2],ans_average[3],ans_average[4])));
//                        Log.d(myTAG, String.format("地图放大手势识别的相似度：%f",ans_totalAver));
//                        Log.d(myTAG, "\n地图放大手势当前序列的长度:"+num3.recordingHistor[0].size());
//                        // 将地图放大
//                        aaMap.moveCamera(CameraUpdateFactory.zoomIn());
//                        // 进行识别序列的清空
//                        myRecordinghistoryClear();
//                        ans[0].clear();
//                        ans[1].clear();
//                    }
//                }
//                // 对于没有识别成功的识别序列，需要将过长的序列删除，接收下一个动作
//                if(num4.recordingHistor[0].size()>num4.trainingHistory[0].size()+3){
//                    // 需要对地图放大手势进行清空
//                    // 对识别序列进行清空
//                    num3.recordingHistor[0].clear();
//                    num3.recordingHistor[1].clear();
//                    num4.recordingHistor[0].clear();
//                    num4.recordingHistor[1].clear();
//                    num6.recordingHistor[0].clear();
//                    num6.recordingHistor[1].clear();
//                    num7.recordingHistor[0].clear();
//                    num7.recordingHistor[1].clear();
//                    num8.recordingHistor[0].clear();
//                    num8.recordingHistor[1].clear();
//                }else if(num40.recordingHistor[0].size()>num40.trainingHistory[0].size()+3){
//                    // 对缩小手势的识别序列进行清空
//                    num30.recordingHistor[0].clear();
//                    num30.recordingHistor[1].clear();
//                    num40.recordingHistor[0].clear();
//                    num40.recordingHistor[1].clear();
//                    num60.recordingHistor[0].clear();
//                    num60.recordingHistor[1].clear();
//                    num70.recordingHistor[0].clear();
//                    num70.recordingHistor[1].clear();
//                    num80.recordingHistor[0].clear();
//                    num80.recordingHistor[1].clear();
//                }
//            }
//            Log.d(myTAG, "myDragMap当前对应的横坐标"+temp_x+"当前对应的纵坐标"+temp_y);
            // : 9/23/2022
            /*
            old version 地图缩放控制函数
            对于手指方向的判断
                如果手指处于扩展的趋势，地图进行放大
                如果手指处于收缩的趋势，地图进行缩小
             */
            int flag_zoom=0;//默认是进行地图的放大
            float temp_finger_dist=(temp_y4-temp_y8)*image_height;// 计算两个关键手指的间距(结果保证为正数)
            float diff_finger_dist=temp_finger_dist-MapZoom_prev_finger_dist;// 计算关键手指间距前后的差异
            Log.d(myTAG, "现在手指的间距："+temp_finger_dist+" 之前手指的间距:"+MapZoom_prev_finger_dist+" 前后手指间距的差异:"+diff_finger_dist);
            MapZoom_prev_finger_dist=temp_finger_dist;// 记录当前手指间距情况
            /*
                判断手指是否在移动的过程中
                    如果手指保持在一个位置，表示用户需要将地图的大小保持在这个位置
                    因此需要将变化范围在一个阈值内的情况过滤出来，不进行地图的缩放
                记录指尖在同一个位置出现的次数 mapZoom_samePoint_times
                    如果指尖多次重复在同一个位置出现，表示用户当前不希望更改当前地图的缩放程度
             */
            // 当手掌在同一个位置保持
            if(Math.abs(diff_finger_dist)<=10){
                // 经过实验，手指保持在同一位置时，前后间距的差异在单位7以内
                mapZoom_samePoint_times++;
                Log.d(myTAG, "myZoommap: 当前指尖位置被识别的次数:"+mapZoom_samePoint_times);
                /*
                如果指尖在同一个位置进行了多次保存，需要提示用户当前地图的缩放操作已经停止，进入到其余手势的识别中
                 */
                if(mapZoom_samePoint_times==20){
                    // 当手指在相同位置保持了20次
//                    Toast.makeText(this,"当前地图缩放已经定位",Toast.LENGTH_SHORT).show();
                    send_message_to_bundle("当前地图的缩放已经定位，进入到其余手势的识别过程中");
                    return_pause=true;//将mediapipe手势识别的线程暂停
                    /*
                        注意，当前对于缩放手势的判断属于一个单独的线程，在当前线程暂停（使用thread.sleep仅仅是将当前的线程暂停）
                        但是上面获得关键点坐标的线程仍然处于运行的状态中
                        因此，会出现当前线程解决后，暂停过程中关键点的坐标仍然被保留，并且线程结束暂停后继续被处理
                        解决办法：当return_pause标志有效，将获得的数据包扔掉（不做处理）
                     */
                    Log.d(myTAG, "myZoommap: 当前地图的缩放已经定位，进入到其余手势的识别过程中");
                    num_change_map=0;
                    flag_Mapcontrol=0;//进入到其余手势的识别中,并且作为
//                    try {
//                        Thread.sleep(3000);//当前的线程睡眠1s
//                    }catch (Exception e){}
                }
                return;//当前变化的范围过小，不属于地图缩放的范围
            }
            mapZoom_samePoint_times=0;// 当指尖从新的位置离开的时候，次数需要清零
            //获得地图当前显示的位置情况
            CameraPosition mCameraposition=null;
            mCameraposition=aaMap.getCameraPosition();
            CameraUpdate mCameraUpdate=null;
            /*
            按照点位前后的相对移动距离，实现地图视角的缩放
                其中 地图视角对应的经度和维度、俯仰程度保持相同
                当前测试：zoom数值越大，地图越放大
                标准情况下zoom对应的值是10
             */
            //当前地图的缩放情况
            float map_zoom_now=mCameraposition.zoom;
            float zoom_size=0;
            if(diff_finger_dist<0){
                // 当前手指指尖呈现出缩小的趋势 地图缩小
                aaMap.moveCamera(CameraUpdateFactory.zoomOut());
//                zoom_size= (float) -1;
            }else{
                // 手指呈现出扩张的趋势 地图放大
                aaMap.moveCamera(CameraUpdateFactory.zoomIn());
//                zoom_size= (float)1;
            }
//            Log.d(myTAG, "当前地图的缩放情况:"+map_zoom_now);
//            mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude,mCameraposition.target.longitude),map_zoom_now+zoom_size,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
//            aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
        }else{
            flag_Mapcontrol=0;// 当前的手势不满足缩放手势，退回到静态手势识别中
        }
//        else{
////            Log.d(myTAG, "进行地图缩小手势的识别/当前手势不属于changevol");
////            Log.d(myTAG, "缩小手势序列的长度: "+num40.recordingHistor[0].size());
////            /*
////            其中地图缩小寿手势的操作一般在当前代码中被分类
////             */
////            // 可能是静态手势不满足，退出地图缩放的操作
////            flag_Mapcontrol=0;//重新退回到手势识别的过程中
////            // 如果已经记录一部分序列，有可能是因为手势提前完成，也需要计算一次相似度
////            // 对地图缩小手势的识别
////            if(num40.recordingHistor[0].size()!=0){
////                // 当记录序列的长度达到模板序列长度的要求 选择使用DTW计算两个序列的相似度
////                // 创建DTW算法的类
////                final DTW lDTW= new DTW();
////                // 记录DTW计算的结果 并且包含两个维度的结果
////                List<Double>[]ans=new List[]{new ArrayList(),new ArrayList()};
////                // 数据的预处理 转换成以序列第一个点为原点的坐标(使用坐标的相对位置关系)
//////                myPreview(num30.recordingHistor[0]);
//////                myPreview(num30.recordingHistor[1]);
////                myPreview(num40.recordingHistor[0]);
////                myPreview(num40.recordingHistor[1]);
//////                myPreview(num60.recordingHistor[0]);
//////                myPreview(num60.recordingHistor[1]);
//////                myPreview(num70.recordingHistor[0]);
//////                myPreview(num70.recordingHistor[1]);
////                myPreview(num80.recordingHistor[0]);
////                myPreview(num80.recordingHistor[1]);
////                // 对每个点的两个坐标计算
//////                ans[0].add(lDTW.compute(primitive(num30.recordingHistor[0]),primitive(num30.trainingHistory[0])).getDistance());// x
//////                ans[1].add(lDTW.compute(primitive(num30.recordingHistor[1]),primitive(num30.trainingHistory[1])).getDistance());// y
////                ans[0].add(lDTW.compute(primitive(num40.recordingHistor[0]),primitive(num40.trainingHistory[0])).getDistance());// x
////                ans[1].add(lDTW.compute(primitive(num40.recordingHistor[1]),primitive(num40.trainingHistory[1])).getDistance());// y
//////                ans[0].add(lDTW.compute(primitive(num60.recordingHistor[0]),primitive(num60.trainingHistory[0])).getDistance());// x
//////                ans[1].add(lDTW.compute(primitive(num60.recordingHistor[1]),primitive(num60.trainingHistory[1])).getDistance());// y
//////                ans[0].add(lDTW.compute(primitive(num70.recordingHistor[0]),primitive(num70.trainingHistory[0])).getDistance());// x
//////                ans[1].add(lDTW.compute(primitive(num70.recordingHistor[1]),primitive(num70.trainingHistory[1])).getDistance());// y
////                ans[0].add(lDTW.compute(primitive(num80.recordingHistor[0]),primitive(num80.trainingHistory[0])).getDistance());// x
////                ans[1].add(lDTW.compute(primitive(num80.recordingHistor[1]),primitive(num80.trainingHistory[1])).getDistance());// y
////                // 根据计算的结果判断分类情况
////                int n_keypoints=2;// 设定的关键点的数量
////                double[]ans_average=new double[n_keypoints];
////                // 设定按照x y两个方向上距离的平均值进行衡量
////                for(int i=0;i<n_keypoints;i++){
////                    ans_average[i]=(ans[0].get(i)+ans[1].get(i))/2;
////                }
////                double ans_sum=0,ans_totalAver;
////                // 设定按照x y两个方向上距离的平均值进行衡量
////                for(int i=0;i<n_keypoints;i++){
////                    ans_average[i]=(ans[0].get(i)+ans[1].get(i))/2;
////                    ans_sum+=ans_average[i];
////                }
////                ans_totalAver=ans_sum/n_keypoints;// 计算所有关键点的平均相似度
////                /*
////                DTW手势分类阈值的修改
////                */
////                if(ans_totalAver<=0.5&&ans_totalAver>0.1){
//////                    Log.d(myTAG, (String.format("当前计算结果(相似度的平均值):\nnum3:%f num4:%f num6:%f num7:%f num8:%f\n",ans_average[0],ans_average[1],ans_average[2],ans_average[3],ans_average[4])));
////                    Log.d(myTAG, String.format("地图缩小手势的相似度：%f",ans_totalAver));
////                    // 将地图缩小
////                    aaMap.moveCamera(CameraUpdateFactory.zoomOut());
////                    // 对识别序列的清空
////                    myRecordinghistoryClear();
////                }
////            }
//        }
    }

    /**
     * 对识别序列的清空
     */
    private void myRecordinghistoryClear() {
        // 对识别序列进行清空
        num3.recordingHistor[0].clear();
        num3.recordingHistor[1].clear();
        num4.recordingHistor[0].clear();
        num4.recordingHistor[1].clear();
        num6.recordingHistor[0].clear();
        num6.recordingHistor[1].clear();
        num7.recordingHistor[0].clear();
        num7.recordingHistor[1].clear();
        num8.recordingHistor[0].clear();
        num8.recordingHistor[1].clear();
        // 对于地图缩小手势识别序列的清空
        num30.recordingHistor[0].clear();
        num30.recordingHistor[1].clear();
        num40.recordingHistor[0].clear();
        num40.recordingHistor[1].clear();
        num60.recordingHistor[0].clear();
        num60.recordingHistor[1].clear();
        num70.recordingHistor[0].clear();
        num70.recordingHistor[1].clear();
        num80.recordingHistor[0].clear();
        num80.recordingHistor[1].clear();
    }

    /**
     * DTW 使用到的数据预处理的方法
     * @param mylist 一个arraylist列表
     */
    private void myPreview(List<Float> mylist) {
        float base=0;
        for(int i=0;i<mylist.size();i++){
            if(i==0){
                // 记录起点
                base=mylist.get(0);
            }else {
                // 将序列中的每个点减去起点
                float temp=mylist.get(i)-base;
                mylist.set(i,temp);
            }
        }
    }

    /**
     * Converts a List of Floats into a primitive equivalent.
     */
    // 将list类型转换为数组类型
    private static final float[] primitive(final List<Float> pList) {
        // Declare the Array.
        final float[] lT = new float[pList.size()];
        // Iterate the List.
        for (int i = 0; i < pList.size(); i++) {
            // Buffer the Element.
            lT[i] = pList.get(i);
        }
        // Return the Array.
        return lT;
    }
    //修改进度条
    private void change_the_bar(int change_num) {
        progressBar.setProgress(max(0, min(change_num * 4, 100)));
    }

    //弹窗提示
    private void pop_toast(int photo_id) {
        Toast customToast = new Toast(getApplicationContext());
        //获得view的布局
        View customView = LayoutInflater.from(getApplicationContext()).inflate(R.layout.custom_toast, null);
        ImageView img = (ImageView) customView.findViewById(R.id.toast_image);
        //设置ImageView的图片
        img.setBackgroundResource(photo_id);

        //设置toast的View,Duration,Gravity最后显示
        customToast.setView(customView);
        customToast.setDuration(Toast.LENGTH_SHORT);
        customToast.setGravity(Gravity.CENTER, 0, 0);
        customToast.show();
    }

    //初始化菜单
    private void initFruits() {
        fruitList.clear();

        SharedPreferences prefs = PreferenceManager.getDefaultSharedPreferences(this);
        //放大或缩小地图的图标
        String previous_song_option = prefs.getString("play_previous_song", "0");
        if ("0".equals(previous_song_option)) {
//            Toast.makeText(MapControl.this,"放大地图", Toast.LENGTH_SHORT).show();
            MainMenu next_song_item = new MainMenu("放大或缩小地图", R.drawable.control_vol);
            fruitList.add(next_song_item);

        } else if ("1".equals(previous_song_option)) {
//            Toast.makeText(MapControl.this,"放大地图", Toast.LENGTH_SHORT).show();
            MainMenu next_song_item = new MainMenu("放大或缩小地图", R.drawable.control_vol);
            fruitList.add(next_song_item);
        }
        //按钮对应的缩小地图
        if ("0".equals(previous_song_option)) {
//            Toast.makeText(MapControl.this,"缩小地图", Toast.LENGTH_SHORT).show();
            MainMenu next_song_item = new MainMenu("缩小地图", R.drawable.control_vol);
            fruitList.add(next_song_item);

        } else if ("1".equals(previous_song_option)) {
//            Toast.makeText(MapControl.this,"缩小地图", Toast.LENGTH_SHORT).show();
            MainMenu next_song_item = new MainMenu("缩小地图", R.drawable.control_vol);
            fruitList.add(next_song_item);
        }
        //设置接听电话的图标
        String next_song_option = prefs.getString("play_next_song", "0");
        if ("0".equals(next_song_option)) {
            MainMenu next_song_item = new MainMenu("接听电话", R.drawable.six);
            fruitList.add(next_song_item);

        } else if ("1".equals(next_song_option)) {
            MainMenu next_song_item = new MainMenu("接听电话", R.drawable.six);
            fruitList.add(next_song_item);
        }

        //设置绝句电话的图标
        String stop_song_option = prefs.getString("stop_the_song", "0");
        if ("0".equals(stop_song_option)) {
            MainMenu next_song_item = new MainMenu("拒绝电话", R.drawable.handstopmusic);
            fruitList.add(next_song_item);

        } else if ("1".equals(stop_song_option)) {
            MainMenu next_song_item = new MainMenu("拒绝电话", R.drawable.handstopmusic);
            fruitList.add(next_song_item);
        }


        MainMenu finish_app = new MainMenu("退出", R.drawable.finish_sign);
        fruitList.add(finish_app);
    }


    protected void play(int which_mp3) {
        MediaPlayer mpMediaPlayer = null;
        mpMediaPlayer = MediaPlayer.create(this, which_mp3);
        try {
            mpMediaPlayer.prepare();
        } catch (IllegalStateException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        mpMediaPlayer.start();
    }

    private void doAction(Integer title) {
        Runtime runtime = Runtime.getRuntime();
        if (title == 0) {//退出的手势
            finish();
        } else if (title == 1) {//接听电话的手势
            if(Phone_process_key==1){
                PhoneFlag=1;
//                ansdenyPhone();
                flagControlPhone();
                Phone_process_key=0;//已经进行处理 在下一个电话到来前将控制封锁
            }
//            try {
//                runtime.exec("input keyevent " + KeyEvent.KEYCODE_MEDIA_PREVIOUS);
//            } catch (Exception e) { // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
        }else if(title==2){//拒绝电话的手势
            if(Phone_process_key==1){
                PhoneFlag=2;
//                ansdenyPhone();
                flagControlPhone();
                Phone_process_key=0;//已经进行处理 在下一个电话到来前将控制封锁
            }
//            try {
//                runtime.exec("input keyevent " + KeyEvent.KEYCODE_MEDIA_PREVIOUS);
//            } catch (Exception e) { // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
        }else if(title==3){//重新定位的手势
            //设置地图控制的局部变量
            AMap aaMap=null;
            if(aaMap==null){
                aaMap=mMapView.getMap();//获得当前
            }
//            Log.d("723maptest", "doAction: 进行定位");
            aaMap.setMyLocationEnabled(true);//点按按钮之后再触发定位 修改 当前应该只是将定位信息重新在地图上显示
            Log.d(myTAG, "展示地图定位: ");
//            try {
//                runtime.exec("input keyevent " + KeyEvent.KEYCODE_MEDIA_PREVIOUS);
//            } catch (Exception e) { // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
        }
        /**
         * 使用启发式方法实现对手势的识别
         */
        else if(title==5)// TODO: 8/18/2022 将地图拖拽对应的手势实现的动作进行替换，需要实现实时拖拽的部分在函数HandleTheHands中
        {
            // 重点：使用启发式算法得到的动态手势识别效果 实现地图的上下移动情况
            AMap aaMap=null;
            if(aaMap==null){
                aaMap=mMapView.getMap();//获得当前
            }
            pre_process_point_history_landmark(point_history);//对于获得的关键点序列进行预处理
            point_history.clear();//完成操作，进行清空等候下一轮
            int point_ans=point_history_classifier();//对轨迹进行分类
            /*
            完成手势的分类之后，对于记录横纵坐标的列表需要进行清空
             */
            point_catchY.clear();
            point_catchX.clear();
            /*
            实现手势识别完成，进入到地图拖拽的界面
             */
            if(point_ans==1){
                //手指右移
//                Toast.makeText(MapControl.this,"上移",Toast.LENGTH_SHORT).show();
                Log.d(myTAG, "doAction: 右移");
                // : 8/12/2022  地图的移动 选择通过获得当前位置的坐标 之后再当前位置坐标上下左右更改 再将地图定位到修改后的坐标
                //根据转入的屏幕位置返回一个地图位置（经纬度）
                //参数依次是：视角调整区域的中心点坐标、希望调整到的缩放级别、俯仰角0°~45°（垂直与地图时为0）、偏航角 0~360° (正北方为0)
//                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(39.977290,116.337000),18,30,0)); 样例
                CameraPosition mCameraposition=null;
                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
//                Log.d(myTAG, "当前位置: "+mCameraposition.target.latitude+", "+mCameraposition.target.longitude);
                //参数latitude代表的是维度 longitude代表的是经度
                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude,mCameraposition.target.longitude-0.01),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
            }else if(point_ans==2){
                Log.d(myTAG, "doAction: 左移");
                CameraPosition mCameraposition=null;
                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude,mCameraposition.target.longitude+0.01),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
            }else if(point_ans==3){
                Log.d(myTAG, "doAction: 下移");
                CameraPosition mCameraposition=null;
                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude-0.1,mCameraposition.target.longitude),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
            }else if(point_ans==4){
                Log.d(myTAG, "doAction: 上移");
                CameraPosition mCameraposition=null;
                mCameraposition=aaMap.getCameraPosition(); //获得地图当前的位置
                CameraUpdate mCameraUpdate = CameraUpdateFactory.newCameraPosition(new CameraPosition(new LatLng(mCameraposition.target.latitude+0.1,mCameraposition.target.longitude),mCameraposition.zoom,mCameraposition.tilt,mCameraposition.bearing));;//其中参数v表示的是地图视图缩放的大小，数值越大放大的越大
                aaMap.moveCamera(mCameraUpdate);//将移动过的地图视图位置进行更新
            }
        }// TODO: 8/10/2022 在25次识别静态手势的时候，记录25个中指之间运动点位，每个5个点位进行一次抽样，按照坐标变化情况判断手指移动轨迹 地图做出相应的响应 
        // TODO: 8/12/2022 修改为对应的手势进入到地图锁定状态 并且按照指尖的坐标将地图的中心位置进行变化 
        try {
            Thread.sleep(500);
        } catch (Exception e) {
            e.printStackTrace();
        }
//        Long upp = Long.valueOf("1500000000");
//
//        for (long i = 0; i <= upp; i++) {
//            long aa = i;
//
//        }
    }

    private int point_history_classifier() {
        //进行轨迹判别 只需要判断轨迹对应坐标的符号是否统一就可以 因为正常的轨迹中是一定满足到手掌原点的距离不断增加的情况
        //如果 归一化之后x均为正 向上移动
        Log.d(myTAG, "Y+"+point_catchY.get(0).toString()+point_catchY.get(1).toString()+" "+point_catchY.get(2).toString()+" "+point_catchY.get(3).toString()+" "+point_catchY.get(4).toString());
        Log.d(myTAG, "X+"+point_catchX.get(0).toString()+point_catchX.get(1).toString()+" "+point_catchX.get(2).toString()+" "+point_catchX.get(3).toString()+" "+point_catchX.get(4).toString());
        int i;
        float Xfinal=point_catchX.get(point_catchX.size()-1);
        float Yfinal=point_catchY.get(point_catchY.size()-1);
        for(i=0;i<point_catchX.size();i++){
            if(point_catchX.get(i)<0){
                break;
            }
        }
        if(i==point_catchX.size()&&Math.abs(Yfinal)<=5){
            //x全部为正数
            return 1;
        }
        for(i=0;i<point_catchX.size();i++){
            if(point_catchX.get(i)>0){
                break;
            }
        }
        if(i==point_catchX.size()&&Math.abs(Yfinal)<=5){
            return 2;//向右移动
        }
        for(i=0;i<point_catchY.size();i++){
            if(point_catchY.get(i)<0){
                break;
            }
        }
        if(i==point_catchY.size()){//上方已经完成对于左右方向上x的判断，下面进行的竖直方向上y的判断，不需要再考虑x的影响
            //y下移
            return 3;
        }
        for(i=0;i<point_catchY.size();i++){
            if(point_catchY.get(i)>0){
                break;
            }
        }
        if(i==point_catchY.size()){
            //y上移
            return 4;
        }
        return 0;
    }

    private void pre_process_point_history_landmark(List<float[]> point_history) {
        int index_temp_land = 0;//计数 判断当前达到模型要求的点位数量与否
        int alllen = point_history.size();//当前记录点位的数量
        Float mx = Float.valueOf(-1000);//记录一维序列output中的最大值
        float base_x = 0, base_y = 0;
        for (int i = 0; i < upper_limit; i += myInternal) {
            float[] temp_arr = point_history.get(i);
            if (i == 0) {
                //记录基准点的坐标 也就是说 指尖的动态手势对应的相对坐标是相对于第一个坐标点
                base_x = temp_arr[0];
                base_y = temp_arr[1];
            }
            //对得到的坐标转换为相对值 并且进行归一化
//            point_catchX.add((temp_arr[0] - base_x) );
//            point_catchY.add((temp_arr[1] - base_y) );
            point_catchX.add((temp_arr[0] - base_x) / image_width*100);
            point_catchY.add((temp_arr[1] - base_y) / image_height*100);
        }
    }

    private int PhoneFlag=0;
    private int Phone_process_key=0;//避免出现没有来电时候 手势或按键触发识别 导致读取空指针
    protected void onResume() {

        super.onResume();
        //onResume中进行重新绘制加载地图
        mMapView.onResume();
        initFruits();
        MenuAdapter adapter = new MenuAdapter(this, R.layout.main_menu_ui_item, fruitList);
        ListView listView = (ListView) findViewById(R.id.list_view_music);
        listView.setAdapter(adapter);

        next_song = 0;
        converter = new ExternalTextureConverter(eglManager.getContext());
        converter.setFlipY(FLIP_FRAMES_VERTICALLY);
        converter.setConsumer(processor);

        /*
        关于地图和定位时使用到的相关权限的授予
            现在将授予界面转移到MainActivity中
         */
        if (PermissionHelper.cameraPermissionsGranted(this)) {
            startCamera();
        }//相机的权限被集成在jar包中
        //如果没有授予READ_PHONE_STATE权限 电话权限的授予
        if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ANSWER_PHONE_CALLS) != PackageManager.PERMISSION_GRANTED){
            //跳转授权界面
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ANSWER_PHONE_CALLS}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_COARSE_LOCATION}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_FINE_LOCATION}, 1);
        }
        else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_WIFI_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_WIFI_STATE}, 1);
        }
        else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.WRITE_EXTERNAL_STORAGE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.WRITE_EXTERNAL_STORAGE}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_NETWORK_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_NETWORK_STATE}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.CHANGE_WIFI_STATE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.CHANGE_WIFI_STATE}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.INTERNET) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.INTERNET}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_LOCATION_EXTRA_COMMANDS) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_LOCATION_EXTRA_COMMANDS}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.FOREGROUND_SERVICE) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.FOREGROUND_SERVICE}, 1);
        }else if(ContextCompat.checkSelfPermission(this, Manifest.
                permission.ACCESS_BACKGROUND_LOCATION) != PackageManager.PERMISSION_GRANTED){//网络定位的权限的获取
            ActivityCompat.requestPermissions(this, new
                    String[]{ Manifest.permission.ACCESS_BACKGROUND_LOCATION}, 1);
        }

//        //获取系统的TelephonyManager管理器
//        tManager = (TelephonyManager) getSystemService(TELEPHONY_SERVICE);
//        pListener = new PhoneStateListener(){
//            @SuppressLint("MissingPermission")
//            @RequiresApi(api = Build.VERSION_CODES.P)
//            @Override
//            public void onCallStateChanged(int state, String incomingNumber) {
//                Log.d("717", "onResume:来电显示");
//                switch(state)
//                {
//                    case TelephonyManager.CALL_STATE_IDLE:break;//空闲（无呼入或已挂机）
//                    case TelephonyManager.CALL_STATE_OFFHOOK:break;//摘机（有呼入）
//                    //当有电话拨入时
//                    case TelephonyManager.CALL_STATE_RINGING:
//                        Toast.makeText(MapControl.this,"当前拨入的电话号是:"+incomingNumber, Toast.LENGTH_SHORT).show();
//                        Phone_process_key=1;//当前有电话拨入 手势和按键的操作被解除
//                        break;
//                }
//                super.onCallStateChanged(state, incomingNumber);
//            }
//        };
//        tManager.listen(pListener, PhoneStateListener.LISTEN_CALL_STATE);
    }

    @Override
    protected void onPause() {

        super.onPause();
        converter.close();
        mMapView.onPause();//暂停地图的绘制
    }
    @Override
    protected void onDestroy() {//存疑
        //5 最后一步 停止定位
        mLocationClient.stopLocation();//停止定位后，本地定位服务并不会被销毁
        //在activity执行onDestroy时执行mMapView.onDestroy()，销毁地图
        mMapView.onDestroy();
        super.onDestroy();
    }
    //动态权限获取
    //建议在onResume（每次打开这个activity都会加载onResume）中加入权限检查，不要在onCreate中（只在第一次打开activity时，才会加载onCreate）加。第一次授予权限以后，在应用还没被杀死的时候，再将权限拒绝，后面的问题无法避免。
    //https://blog.csdn.net/m0_50408097/article/details/122346377 其中一部分权限的授予部分在Resume函数中
    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {

        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        PermissionHelper.onRequestPermissionsResult(requestCode, permissions, grantResults);
        switch (requestCode) {
            case 1:
                if (grantResults.length > 0 && grantResults[0] != PackageManager.PERMISSION_GRANTED) {
                    //如果没授予此权限，则结束应用
                    //也可以做其它处理
//                    Log.d("717", "onRequestPermissionsResult: 当前权限未被授予");
                    finish();
                }
                break;
            default:
        }
    }
    @Override
    protected void onSaveInstanceState(Bundle outState) {

        super.onSaveInstanceState(outState);
        mMapView.onSaveInstanceState(outState);//保存地图当前的状态
    }
    // 计算最佳的预览大小
    protected Size computeViewSize(int width, int height) {
        return new Size(width, height);
    }

    protected void onPreviewDisplaySurfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        // 设置预览大小
        Size viewSize = computeViewSize(width, height);
        Size displaySize = cameraHelper.computeDisplaySizeFromViewSize(viewSize);
        // 根据是否旋转调整预览图像大小
        boolean isCameraRotated = cameraHelper.isCameraRotated();
        converter.setSurfaceTextureAndAttachToGLContext(
                previewFrameTexture,
                isCameraRotated ? displaySize.getHeight() : displaySize.getWidth(),
                isCameraRotated ? displaySize.getWidth() : displaySize.getHeight());
    }


    private void setupPreviewDisplayView() {
        previewDisplayView.setVisibility(View.GONE);
        ViewGroup viewGroup = findViewById(R.id.preview_display_layout_music);
        viewGroup.addView(previewDisplayView);

        previewDisplayView
                .getHolder()
                .addCallback(
                        new SurfaceHolder.Callback() {
                            @Override
                            public void surfaceCreated(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(holder.getSurface());
                            }

                            @Override
                            public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
                                onPreviewDisplaySurfaceChanged(holder, format, width, height);
                            }

                            @Override
                            public void surfaceDestroyed(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(null);
                            }
                        });
    }

    // 相机启动后事件
    protected void onCameraStarted(SurfaceTexture surfaceTexture) {
        // 显示预览
        previewFrameTexture = surfaceTexture;
        previewDisplayView.setVisibility(View.VISIBLE);
    }

    // 设置相机大小
    protected Size cameraTargetResolution() {
        return null;
    }

    // 启动相机
    public void startCamera() {
        cameraHelper = new CameraXPreviewHelper();
        cameraHelper.setOnCameraStartedListener(this::onCameraStarted);
        CameraHelper.CameraFacing cameraFacing =
                USE_FRONT_CAMERA ? CameraHelper.CameraFacing.FRONT : CameraHelper.CameraFacing.BACK;
        cameraHelper.startCamera(this, cameraFacing, null, cameraTargetResolution());
    }

    // 解析关键点
    private static String getLandmarksDebugString(LandmarkProto.NormalizedLandmarkList landmarks) {
        int landmarkIndex = 0;
        StringBuilder landmarksString = new StringBuilder();
        for (LandmarkProto.NormalizedLandmark landmark : landmarks.getLandmarkList()) {
            landmarksString.append("\t\tLandmark[").append(landmarkIndex).append("]: (").append(landmark.getX()).append(", ").append(landmark.getY()).append(", ").append(landmark.getZ()).append(")\n");
            ++landmarkIndex;
        }
        return landmarksString.toString();
    }

    //接听拒绝电话
    private void ansdenyPhone()
    {
        //获取系统的TelephonyManager管理器
        tManager = (TelephonyManager) getSystemService(TELEPHONY_SERVICE);
        pListener = new PhoneStateListener(){
            @SuppressLint("MissingPermission")
            @RequiresApi(api = Build.VERSION_CODES.P)
            @Override
            public void onCallStateChanged(int state, String incomingNumber) {
                Log.d("717", "ansdenyPhone:现在进行处理");
                switch(state)
                {
                    case TelephonyManager.CALL_STATE_IDLE:break;//空闲（无呼入或已挂机）
                    case TelephonyManager.CALL_STATE_OFFHOOK:break;//摘机（有呼入）
                    //当有电话拨入时
                    case TelephonyManager.CALL_STATE_RINGING:
                        Toast.makeText(MapControl.this,"当前拨入的电话号是:"+incomingNumber, Toast.LENGTH_SHORT).show();
                        Phone_process_key=1;//当前有电话拨入 手势和按键的操作被解除
                        //一定注意 需要在手机上手动对app授权（拨打电话 获得手机通话记录)
                        Log.d("717", "ansdenyPhone: 需要挂断电话");
                        try
                        {
                            //Android10以前挂断电话的方法
//                                Method method = Class.forName("android.os.ServiceManager")
//                                        .getMethod("getService", String.class);
//                                // 获取远程TELEPHONY_SERVICE的IBinder对象的代理
//                                IBinder binder = (IBinder) method.invoke(null,
//                                        new Object[] { TELEPHONY_SERVICE });
//                                // 将IBinder对象的代理转换为ITelephony对象
//                                ITelephony telephony = ITelephony.Stub.asInterface(binder);
//                                // 挂断电话
//                                telephony.endCall();
                            TelecomManager tcm = (TelecomManager)getSystemService(TELECOM_SERVICE);
                            if (PhoneFlag==1)//接听电话
                            {
                                tcm.acceptRingingCall();
                                PhoneFlag=0;
                            }else if(PhoneFlag==2)//拒绝电话
                            {
                                tcm.endCall();
                                PhoneFlag=0;
                            }
                            //要求 需要能够动态赋予权限 但是这样似乎就不需要ITtelephony的接口啦
                        }catch(Exception e){e.printStackTrace();}
                        break;
                }
                super.onCallStateChanged(state, incomingNumber);
            }
        };
        tManager.listen(pListener, PhoneStateListener.LISTEN_CALL_STATE);
    }
    private void flagControlPhone()
    {
        try {

            TelecomManager tcm = (TelecomManager)getSystemService(TELECOM_SERVICE);
            if (PhoneFlag==1)//接听电话
            {
                tcm.acceptRingingCall();
                PhoneFlag=0;
            }else if(PhoneFlag==2)//拒绝电话
            {
                tcm.endCall();
                PhoneFlag=0;
            }
        }catch (Exception e){e.printStackTrace();}
    }
}